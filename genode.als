module genode

sig State {
  kos : set KernelObject,
  pds : set PDom,
  cspace_map : PDom -> one CSpace
} {
  all pd1, pd2 : pds | pd1.cspace_map = pd2.cspace_map => pd1 = pd2
}

sig CapId {}

sig KernelObject {} { all s : State | this in s.kos }
sig CSpace extends KernelObject {
  cap_slots : CapId -> lone KernelObject
}
sig IdentityObject extends KernelObject {}

sig GenodeObject {} {
  all s : State | some pd : s.pds | this in pd.objs
}
sig RPCObject extends GenodeObject {
  owns : one IdentityObject
}

sig PDom {
  objs : set GenodeObject,
  caps : set CapId
} {
  all s : State | this in s.pds
}

fact GenodeAssms {
  all r1, r2 : RPCObject, i : IdentityObject |
    r1.owns = i && r2.owns != i
}

pred example {}

run example for 2

pred create_RPCObject [
    s, s' : State,
    p : PDom, r : RPCObject, i : IdentityObject, c : CapId
] {
  r !in p.objs
  i !in s.kos
  c !in p.caps
}
