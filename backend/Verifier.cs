
/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Z3;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        private static readonly int UNKNOWN = 0;
        private static readonly int VERIFIED_OK = 1;
        private static readonly int VERIFIED_FAIL = -1;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public int Apply(IRMain cfg)
        {
            List<BasicPath> basicPaths = GenBasicPaths(cfg);
            
            // writer.WriteLine("BasicPaths: ");
            // foreach (BasicPath bp in basicPaths)
            // {
            //     bp.Print(writer);
            // }
            // writer.Write("\n");
            
            List<VerificationCondition> verificationConditions = basicPaths
                .Select(bp => new VerificationCondition(bp))
                .ToList();
            foreach (Predicate p in cfg.predicates) { solver.definePredicate(p); }
            bool allValid = verificationConditions.All(vc => vc.Valid(solver));
            
            // writer.WriteLine("Verification Conditions: ");
            // foreach (VerificationCondition vc in verificationConditions)
            // {
            //     vc.Print(writer);
            //     writer.WriteLine($"valid = {vc.Valid(solver)}\n");
            // }
            // writer.Write("\n");
            
            return allValid ? VERIFIED_OK : VERIFIED_FAIL;
        }

        private List<BasicPath> GenBasicPaths(IRMain cfg)
        {
            List<BasicPath> basicPaths = new List<BasicPath>();
            foreach (Function func in cfg.functions)
            {
                SearchBasicBlocks(
                    func.preconditionBlock, 
                    func.preconditionBlock, 
                    0, 
                    basicPaths, 
                    new List<Statement>());
                foreach (Block block in func.blocks)
                {
                    if (block is HeadBlock)
                    {
                        Debug.Assert(block is LoopHeadBlock, "A HeadBlock is not a LoopHeadBlock in func.blocks");
                        SearchBasicBlocks(
                            block,
                            block,
                            0, 
                            basicPaths,
                            new List<Statement>());
                    }
                }
            }
            return basicPaths;
        }

        private void SearchBasicBlocks(
            Block headBlock, Block currBlock, 
            int step, List<BasicPath> basicPaths, List<Statement> statements)
        {
            if (step > 0 && (currBlock is PostconditionBlock || currBlock is LoopHeadBlock))
            {
                BasicPath basicPath = VerifierUtils.BasicPathConstructor(
                    headBlock,
                    currBlock,
                    VerifierUtils.GetHeadConditions(headBlock),
                    VerifierUtils.GetTailConditions(currBlock),
                    statements,
                    VerifierUtils.GetRankingFunctions(headBlock),
                    VerifierUtils.GetRankingFunctions(currBlock));
                basicPaths.Add(basicPath);
                return;
            }

            int addedStmtCount = 0;
            foreach (Statement stmt in currBlock.statements)
            {
                if (stmt is AssignStatement || stmt is AssumeStatement)
                {
                    statements.Add(stmt);
                    ++addedStmtCount;
                } else if (stmt is AssertStatement assertStmt)
                {
                    BasicPath basicPath = VerifierUtils.BasicPathConstructor(
                        headBlock,
                        currBlock,
                        VerifierUtils.GetHeadConditions(headBlock),
                        new List<Expression>() {assertStmt.pred},
                        statements,
                        VerifierUtils.GetRankingFunctions(headBlock),
                        null // no need to check ranking functions here
                        );
                    basicPaths.Add(basicPath);
                } else if (stmt is FunctionCallStatement funcStmt)
                {
                    BasicPath basicPath = VerifierUtils.BasicPathConstructor(
                        headBlock,
                        currBlock,
                        VerifierUtils.GetHeadConditions(headBlock),
                        VerifierUtils.GetAdjustedFunctionCallPreAssertions(funcStmt),
                        statements,
                        VerifierUtils.GetRankingFunctions(headBlock),
                        VerifierUtils.GetRankingFunctions(funcStmt)
                        );
                    basicPaths.Add(basicPath);
                    AssumeStatement newAssumeStmt = new AssumeStatement();
                    newAssumeStmt.condition = VerifierUtils.BigAndExpConstructor(VerifierUtils.GetAdjustedFunctionCallPostAssumptions(funcStmt));
                    statements.Add(newAssumeStmt);
                    ++addedStmtCount;
                }
                else
                {
                    Debug.Assert(false, "stmt is not in [Assign, Assume, Assert, FuncCall]Stmt");
                }
            }

            foreach (Block succBlock in currBlock.successors)
            {
                SearchBasicBlocks(headBlock, succBlock, step + 1, basicPaths, statements);
            }
            
            // backtracking
            for (int i = 0; i < addedStmtCount; i++) statements.RemoveAt(statements.Count - 1); 
        }

    }

    class VerificationCondition
    {
        public Expression partialCondition;
        public Expression totalCondition;
        public Expression headRankingFunctionGE0Condition;
        public bool checkTermination;
        public bool knowRankingFunctionDescending;
        
        

        public VerificationCondition(BasicPath basicPath)
        {
            checkTermination = false;
            if (basicPath.headRankingFunctions.Count > 0)
            {
                checkTermination = true;
                knowRankingFunctionDescending = (basicPath.tailRankingFunctions.Count == 0);
                headRankingFunctionGE0Condition = VerifierUtils.ImpliesExpConstructor(
                    VerifierUtils.BigAndExpConstructor(basicPath.headConditions),
                    VerifierUtils.BigAndExpConstructor(
                        basicPath.headRankingFunctions
                            .Select(e => VerifierUtils.GE0ExpConstructor(e))
                            .ToList()
                        )
                    );
                if (!knowRankingFunctionDescending)
                {
                    List<Expression> rankingFunctions = new List<Expression>(basicPath.tailRankingFunctions);
                    List<Expression> freshHeadRankingFunctions = basicPath.headRankingFunctions
                        .Select(e => VerifierUtils.FreshCopy(e))
                        .ToList();
                    List<Expression> headRankingFunctionsCopyInvariants = basicPath.headRankingFunctions
                        .Select(e => VerifierUtils.FreshCopyInvariant(e))
                        .ToList();
                    totalCondition = WeakestPreconditionOfStmts(
                        VerifierUtils.LexGTExpConstrutor(
                            freshHeadRankingFunctions,
                            rankingFunctions
                            ), 
                        basicPath.statements
                        );
                    totalCondition = VerifierUtils.ImpliesExpConstructor(
                        VerifierUtils.AndExpConstructor(
                            VerifierUtils.BigAndExpConstructor(headRankingFunctionsCopyInvariants),
                            VerifierUtils.BigAndExpConstructor(basicPath.headConditions)),
                        totalCondition
                        );
                }
            }

            partialCondition = VerifierUtils.BigAndExpConstructor(basicPath.tailConditions);
            partialCondition = WeakestPreconditionOfStmts(partialCondition, basicPath.statements);
            partialCondition = VerifierUtils.ImpliesExpConstructor(
                VerifierUtils.BigAndExpConstructor(basicPath.headConditions),
                partialCondition
                );
        }

        private static Expression WeakestPreconditionOfStmts(Expression exp, List<Statement> stmts)
        {
            for (int i = stmts.Count - 1; i >= 0; i--)
            {
                exp = WeakestPrecondition(exp, stmts[i]);
            } 
            return exp;
        }

        private static Expression WeakestPrecondition(Expression exp, Statement stmt)
        {
            if (stmt is AssumeStatement assume)
            {
                return VerifierUtils.ImpliesExpConstructor(assume.condition, exp);
            } else if (stmt is AssignStatement)
            {
                if (stmt is VariableAssignStatement varAssign)
                {
                    return exp.Substitute(varAssign.variable, varAssign.rhs);
                } else if (stmt is SubscriptAssignStatement subAssign)
                {
                    return exp.Substitute(
                        subAssign.array, 
                        new ArrayUpdateExpression(
                            new VariableExpression(subAssign.array), 
                            subAssign.subscript, 
                            subAssign.rhs, 
                            new VariableExpression(subAssign.array.length)
                            ));
                }
                else
                {
                    Debug.Assert(false, "Unknown stmt type! Neither VarAssign nor SubAssign");
                }
            }
            else
            {
                Debug.Assert(false, "stmt isn't in [Assume, Assert, Assign]Stmt");
            }
            return null;
        }

        public bool Valid(SMTSolver solver)
        {
            bool partialCorrectness = (solver.CheckValid(partialCondition) == null);
            bool termination = true;
            if (checkTermination)
            {
                termination &= (solver.CheckValid(headRankingFunctionGE0Condition) == null);
                if (!knowRankingFunctionDescending)
                {
                    termination &= (solver.CheckValid(totalCondition) == null);
                }
            }
            return partialCorrectness && termination;
        }

        public void Print(TextWriter writer)
        {
            writer.Write("partial condition: ");
            partialCondition.Print(writer);
            writer.Write("\n");
            if (checkTermination)
            {
                if (!knowRankingFunctionDescending)
                {
                    writer.Write("total condition: ");
                    totalCondition.Print(writer);
                    writer.Write("\n");                         
                }
                writer.Write("head ranking function >= 0 condition: ");
                headRankingFunctionGE0Condition.Print(writer);
                writer.Write("\n"); 
            }
        }
    }

    /// <summary>
    /// Verifier 类的辅助类，这些方法正常写应该分配到相应的文件中
    /// </summary>
    static class VerifierUtils
    {

        public static BasicPath BasicPathConstructor(
            Block headBlock, 
            Block tailBlock,
            List<Expression> headConditions,
            List<Expression> tailConditions,
            List<Statement> statements,
            List<Expression>? headRankingFunctions,
            List<Expression>? tailRankingFunctions)
        {
            BasicPath basicPath = new BasicPath();
            basicPath.headBlock = headBlock;
            basicPath.tailBlock = tailBlock;
            basicPath.headConditions = new List<Expression>(headConditions);
            basicPath.tailConditions = new List<Expression>(tailConditions);
            basicPath.statements = new List<Statement>(statements);
            if (headRankingFunctions != null) basicPath.headRankingFunctions = new List<Expression>(headRankingFunctions);
            if (tailRankingFunctions != null) basicPath.tailRankingFunctions = new List<Expression>(tailRankingFunctions);
            return basicPath;
        }

        public static List<Expression> FuncCondsSubstitute(List<Expression> conditions, List<LocalVariable> vars, List<LocalVariable> varExps)
        {
            int n = vars.Count;
            Debug.Assert(n == varExps.Count, "vars.Count != exps.Count");
            List<Expression> exps = varExps
                .Select(v => (Expression)new VariableExpression(v))
                .ToList();
            List<Expression> newConditions = new List<Expression>(conditions);
            for (int i = 0; i < n; i++)
            {
                newConditions = newConditions
                    .Select(cond => cond.Substitute(vars[i], exps[i]))
                    .ToList();
            }
            return newConditions;
        }

        public static List<Expression> GetAdjustedFunctionCallPreAssertions(FunctionCallStatement funcStmt)
        {
            Function function = funcStmt.rhs.function;
            List<Expression> conditions = FuncCondsSubstitute(
                function.preconditionBlock.conditions,
                function.parameters,
                funcStmt.rhs.argumentVariables);
            return conditions;
        }

        public static List<Expression> GetAdjustedFunctionCallPostAssumptions(FunctionCallStatement funcStmt)
        {
            Function function = funcStmt.rhs.function;
            List<Expression> conditions = FuncCondsSubstitute(
                function.postconditionBlock.conditions,
                function.parameters,
                funcStmt.rhs.argumentVariables);
            conditions = FuncCondsSubstitute(
                conditions,
                function.rvs,
                funcStmt.lhs);
            return conditions;
        }

        public static List<Expression> GetHeadConditions(Block headBlock)
        {
            Debug.Assert(headBlock is PreconditionBlock 
                         || headBlock is LoopHeadBlock,
                "headBlock is neither PreconditionBlock nor LoopHeadBlock");
            if (headBlock is PreconditionBlock pre)
            {
                return pre.conditions;
            } 
            if (headBlock is LoopHeadBlock loop)
            {
                return loop.invariants;
            }
            Debug.Assert(false, "cannot reach here");
            return null;
        }

        public static List<Expression> GetTailConditions(Block tailBlock)
        {
            Debug.Assert(tailBlock is PostconditionBlock 
                         || tailBlock is LoopHeadBlock,
                "tailBlock is neither PostconditionBlock nor LoopHeadBlock");
            if (tailBlock is PostconditionBlock post)
            {
                return post.conditions;
            }
            if (tailBlock is LoopHeadBlock loop)
            {
                return loop.invariants;
            }
            Debug.Assert(false, "cannot reach here");
            return null;
        }

        public static List<Expression> GetRankingFunctions(Block block) // loophead or precondition
        {
            if (block is LoopHeadBlock loopHead)
            {
                return loopHead.rankingFunctions;
            } else if (block is PreconditionBlock precondition)
            {
                return precondition.rankingFunctions;
            } else if (block is PostconditionBlock)
            {
                return null;
            }
            else
            {
                Debug.Assert(false, "block is not in [LoopHead, Precondition, Postcondition]");
            }
            return null;
        }

        public static List<Expression> GetRankingFunctions(FunctionCallStatement funcStmt)
        {
            // TODO: adjust ranking functions too
            Function function = funcStmt.rhs.function;
            List<Expression> rankingFunctions = function.preconditionBlock.rankingFunctions;
            rankingFunctions = FuncCondsSubstitute(
                rankingFunctions,
                function.parameters,
                funcStmt.rhs.argumentVariables);
            return rankingFunctions;
        }

        public static Expression ImpliesExpConstructor(Expression a, Expression b)
        {
            // a => b
            return new ImplicationExpression(a, b);
        }

        public static Expression AndExpConstructor(Expression a, Expression b)
        {
            // a && b
            return new AndExpression(a, b);
        }
        
        public static Expression OrExpConstructor(Expression a, Expression b)
        {
            // a || b
            return new OrExpression(a, b);
        }

        public static Expression BigAndExpConstructor(List<Expression> exps)
        {
            Expression ret = new BoolConstantExpression(true);
            foreach (Expression e in exps) ret = AndExpConstructor(ret, e);
            return ret;
        }

        public static Expression GE0ExpConstructor(Expression e)
        {
            // e >= 0
            return new GEExpression(e, new IntConstantExpression(0));
        }

        public static Expression GTExpConstructor(Expression a, Expression b)
        {
            // a > b
            return new GTExpression(a, b);
        }

        public static Expression EQExpConstructor(Expression a, Expression b)
        {
            // a == b
            return new EQExpression(a, b);
        }

        public static Expression LexGTExpConstrutor(List<Expression> a, List<Expression> b)
        {
            // a is lexically greater than b, i.e. a[0] > b[0] || (a[0] == b[0] && (...))
            int n = a.Count;
            Debug.Assert(n == b.Count, "a.Count != b.Count");
            Debug.Assert(n > 0, "list length = 0");
            if (n == 1) return GTExpConstructor(a[0], b[0]);
            List<Expression> a1 = new List<Expression>(a);
            a1.RemoveAt(0);
            List<Expression> b1 = new List<Expression>(b);
            b1.RemoveAt(0);
            return OrExpConstructor(
                GTExpConstructor(a[0], b[0]),
                AndExpConstructor(
                    EQExpConstructor(a[0], b[0]),
                    LexGTExpConstrutor(a1, b1)
                )
            );
        }

        public static Expression FreshCopy(Expression exp)
        {
            HashSet<LocalVariable> localVariables = exp.GetFreeVariables();
            foreach (LocalVariable var in localVariables)
            {
                LocalVariable varCopy = new LocalVariable();
                varCopy.type = var.type;
                varCopy.name = var.name + "_copy";
                exp = exp.Substitute(var, new VariableExpression(varCopy));
            }
            return exp;
        }

        public static Expression FreshCopyInvariant(Expression exp)
        {
            HashSet<LocalVariable> localVariables = exp.GetFreeVariables();
            List<Expression> conditions = new List<Expression>();
            foreach (LocalVariable var in localVariables)
            {
                LocalVariable varCopy = new LocalVariable();
                varCopy.type = var.type;
                varCopy.name = var.name + "_copy";
                conditions.Add(EQExpConstructor(new VariableExpression(var), new VariableExpression(varCopy)));
            }
            return BigAndExpConstructor(conditions);
        }

    }
}

