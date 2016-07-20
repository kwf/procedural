
include "Prelude.dfy"
include "Common.dfy"

type nu = Id

type Sigma = seq<Type>
type sigma = seq<value>

type Phi = seq<(Phi, Sigma)>
type phi = seq<(nu, sigma)>

type Delta = map<nu, Phi>
type delta = map<nu, block>

datatype value = integer(int)
               | boolean(bool)
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
