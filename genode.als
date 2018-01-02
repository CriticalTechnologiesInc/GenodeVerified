module genode

abstract sig Object {}

// Note that this combines Genode's state AND the kernel state
sig State {
  kos : set KernelObject,
  pds : set PDom,
  cspace_map : PDom one->one CSpace
}

fun PDom.cspace : CSpace { this.~pds.cspace_map[this] }

sig CapId {}

sig KernelObject extends Object {} {
  all s : State | this in s.kos
}

// Cap space contains a finite number of slots, each of which may contain a
// capability [Genode Book 3.1.1]
sig CSpace extends KernelObject {
  // this simple model assumes CSpaces are non-recursive (not the case in seL4)
  // [assumption]
  cap_slots : CapId ->lone (KernelObject - CSpace)
}

// An identity object represents an RPC object in the kernel [Genode Book 3.1.1]
sig IdentityObject extends KernelObject {} {
  let owner = this.~owns {
    // Each identity object can have only one owner [implied, Genode Book 3.1.1]
    lone owner
    // Each owned identity object must have an entry reachable from its owner's
    // cspace [assumption]
    one owner => some c : CapId | owner.~objs.cspace.cap_slots[c] = this
  }
}

abstract sig GenodeObject extends Object {} {
  all s : State | some pd : s.pds | this in pd.objs
}

// An RPC object provides an RPC interface [Genode Book 3.1.1]
sig RPCObject extends GenodeObject {
  owns : one IdentityObject
}

sig PDom {
  objs : set GenodeObject,
  caps : set CapId
} {
  all s : State | this in s.pds
  // A capability unambiguously refers to an RPC object [Genode Book 3.1.1]
  all c : caps | some o : RPCObject | o.owns = this.cspace.cap_slots[c]
}

pred example {}
run example for 3 but exactly 1 State, exactly 2 PDom, 10 Object, exactly 3 RPCObject

pred delegate [
    s, s' : State,
    src_pd, dst_pd : PDom, r : RPCObject, i : IdentityObject, c : CapId
] {
  r in src_pd.objs
  i in r.owns
  c !in dst_pd.caps
  //let cap_slots' = dst_pd.cspace.cap_slots ++ {c -> i} |
  //let dst_pd' = 
}
