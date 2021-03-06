
include "Prelude.dfy"
include "Common.dfy"

type nu = Id

type Sigma = List<Type>
type sigma = List<value>

datatype Phi = MkPhi(out: List<(Phi, Sigma)>)
type phi = List<(nu, sigma)>

type Delta = map<nu, Phi>
type delta = map<nu, block>

datatype value = integer(getInteger: int)
               | boolean(getBoolean: bool)
               | unit

datatype operation = binary(Op)
                   | not
                   | const(value)
                   | read(Type)
                   | printf(FormatString)

datatype command = store(nat)
                 | load(nat)
                 | pop(nat)
                 | apply(nat, operation)

datatype jump = goto(nu)
              | branch(nu, nu)
              | call(nat, nu, nu)
              | ret(nat)
              | halt

type block = (List<command>, jump)
