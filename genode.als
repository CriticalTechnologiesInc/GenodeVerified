module genode

abstract sig Object {}

// Note that this combines Genode's state AND the kernel state
sig State {
  kos : set KernelObject,
  pds : set PDom,
  cspace_map : PDom -> one CSpace
} {
  // Genode ensures that cspaces are unique for each protection domain
  all pd1, pd2 : pds | pd1.cspace_map = pd2.cspace_map => pd1 = pd2
}

fun CSpace.reachable : set CSpace {
  let trans = {cs1, cs2 : CSpace |
                 some c : CapId | cs1.@cap_slots[c] = cs2}
  | this.^trans
}

fun PDom.cspace : CSpace { this.~pds.cspace_map[this] }

sig CapId {}

sig KernelObject extends Object {} {
  all s : State | this in s.kos
}
sig CSpace extends KernelObject {
  cap_slots : CapId -> lone KernelObject
} {
  // CSpaces references cannot form cycles
  this !in reachable[this]
}
sig IdentityObject extends KernelObject {} {
  let owner = this.~owns {
    // Each identity object can have only one owner
    lone owner
    // Each owned identity object must have an entry reachable from its owner's
    // cspace
    one owner => some cs : CSpace | cs in reachable[owner.~objs.cspace] &&
                   (some c : CapId | cs.cap_slots[c] = this)
  }
}
assert AccessIFFOwned {
  all i : IdentityObject, pd : PDom | 
}

abstract sig GenodeObject extends Object {} {
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

run example for 3 but exactly 1 State, exactly 2 PDom, 10 Object, exactly 3 RPCObject



pred create_RPCObject [
    s, s' : State,
    p : PDom, r : RPCObject, i : IdentityObject, c : CapId
] {
  r !in p.objs
  i !in s.kos
  c !in p.caps
}
