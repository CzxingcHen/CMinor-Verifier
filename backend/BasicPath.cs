/* Copyright 2022 Xingyu Xie

This file is part of CMinor.

CMinor is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

CMinor is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with CMinor. If not, see <https://www.gnu.org/licenses/>. */

using System.Diagnostics.Contracts;
using System.Collections.Generic;
using System.IO;

namespace cminor
{
    class BasicPath
    {
        public Block headBlock = null;
        public Block tailBlock = null;
        public List<Expression> headConditions = new List<Expression>();
        public List<Expression> headRankingFunctions = new List<Expression>();

        // only assumement, assignment are allowed
        public List<Statement> statements = new List<Statement>();

        public List<Expression> tailConditions = new List<Expression>();

        public List<Expression> tailRankingFunctions = new List<Expression>();

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            foreach (Expression headCondition in headConditions)
                Contract.Invariant(headCondition.type is BoolType);
        }

        public void Print(TextWriter writer)
        {
            writer.Write($"headBlock: {headBlock}\n");
            writer.Write($"tailBlock: {tailBlock}\n");
            
            writer.Write("headConditions: ");
            for (int i = 0; i < headConditions.Count; i++)
            {
                headConditions[i].Print(writer);
                writer.Write(", ");
            }
            writer.Write("\n");
            writer.Write("tailConditions: ");
            for (int i = 0; i < tailConditions.Count; i++)
            {
                tailConditions[i].Print(writer);
                writer.Write(", ");
            }
            writer.Write("\n");
            writer.Write("statements: ");
            for (int i = 0; i < statements.Count; i++)
            {
                statements[i].Print(writer);
                writer.Write(", ");
            }
            writer.Write("\n");
            writer.Write("\n");
        }
    }
}