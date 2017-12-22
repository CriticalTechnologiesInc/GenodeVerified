module genode

// Note that this combines Genode's state AND the kernel state
sig State {
  kos : set KernelObject,
  pds : set PDom,
  cspace_map : PDom -> one CSpace
} {
  all pd1, pd2 : pds | pd1.cspace_map = pd2.cspace_map => pd1 = pd2
}

abstract sig Object {}

sig CapId {}

sig KernelObject extends Object {} {
  all s : State | this in s.kos
}
sig CSpace extends KernelObject {
  cap_slots : CapId -> lone KernelObject
} {
  // CSpaces references cannot form cycles
  let trans = {cs1, cs2 : CSpace |
                 some c : CapId | cs1.@cap_slots[c] = cs2}
  | this !in this.^trans
}
sig IdentityObject extends KernelObject {}

sig GenodeObject extends Object {} {
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

pred example {}

run example for 5 but exactly 1 State, exactly 2 PDom, 3 CapId

pred create_RPCObject [
    s, s' : State,
    p : PDom, r : RPCObject, i : IdentityObject, c : CapId
] {
  r !in p.objs
  i !in s.kos
  c !in p.caps
}
