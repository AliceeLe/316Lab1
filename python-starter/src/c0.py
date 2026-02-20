from dataclasses import dataclass
from typing import List, Optional

@dataclass
class Type:
    pass

@dataclass
class IntType(Type):
    def __repr__(self):
        return "int"

@dataclass
class BoolType(Type):
    def __repr__(self):
        return "bool"

@dataclass
class ArrayType(Type):
    base: Type
    def __repr__(self):
        return f"{self.base}[]"

@dataclass
class Node:
    pass

@dataclass
class Exp(Node):
    pass

@dataclass
class IntConst(Exp):
    value: int

@dataclass
class BoolConst(Exp):
    value: bool

@dataclass
class NullConst(Exp):
    pass

@dataclass
class Var(Exp):
    name: str

@dataclass
class BinOp(Exp):
    op: str
    left: Exp
    right: Exp

@dataclass
class UnOp(Exp):
    op: str
    arg: Exp

@dataclass
class Length(Exp):
    arg: Exp

@dataclass
class ArrayAccess(Exp):
    arr: Exp
    index: Exp

@dataclass
class ForAll(Exp):
    vars: List[str]
    body: Exp

@dataclass
class ResultVar(Exp):
    pass

@dataclass
class ArrMake(Exp):
    """An `int[]` value with a given length and arbitrary (unknown) contents."""
    length: Exp

@dataclass
class ArrSet(Exp):
    """Functional update: returns a new array equal to `arr` except at `index`."""
    arr: Exp
    index: Exp
    val: Exp

@dataclass
class Stmt(Node):
    pass

@dataclass
class Decl(Stmt):
    type: Type
    name: str
    init: Optional[Exp]

@dataclass
class Assign(Stmt):
    dest: str # Variable name
    source: Exp

@dataclass
class AllocArray(Stmt):
    dest: str
    type: Type
    count: Exp

@dataclass
class ArrRead(Stmt):
    dest: str
    arr: Exp
    index: Exp

@dataclass
class ArrWrite(Stmt):
    arr: Exp
    index: Exp
    val: Exp

@dataclass
class Block(Stmt):
    stmts: List[Stmt]

@dataclass
class If(Stmt):
    cond: Exp
    true_branch: Stmt
    false_branch: Optional[Stmt]

@dataclass
class While(Stmt):
    cond: Exp
    invariants: List[Exp]
    body: Stmt

@dataclass
class Assert(Stmt):
    cond: Exp

@dataclass
class Error(Stmt):
    msg: str

@dataclass
class Return(Stmt):
    val: Optional[Exp]

@dataclass
class Program(Node):
    stmts: List[Stmt]
    contracts: List[Exp] = None # List of requires/ensures? Or better specific structure
    # Actually, we need requires and ensures separately.
    requires: List[Exp] = None
    ensures: List[Exp] = None
    args: List[str] = None # ["argc", "argv"] typically, but abstractly
