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
  some s : State | this in s.kos // no floating kernel objects
}

// Cap space contains a finite number of slots, each of which may contain a
// capability [Genode Book 3.1.1]
sig CSpace extends KernelObject {
  // this simple model assumes CSpaces are non-recursive (not the case in seL4)
  // [assumption]
  cap_slots : CapId ->lone (KernelObject - CSpace)
}

// An identity object represents an RPC object in the kernel
// [Genode Book 3.1.1]
sig IdentityObject extends KernelObject {} {
  let owner = this.~owns {
    // Each identity object can have only one owner
    // [implied, Genode Book 3.1.1]
    lone owner
    // Each owned identity object must have an entry reachable from its owner's
    // cspace [assumption]
    one owner => some c : CapId | owner.~objs.cspace.cap_slots[c] = this
  }
}

abstract sig GenodeObject extends Object {} {
  // Genode objects exist in at most one protection domain at a time
  all s : State | lone pd : s.pds | this in pd.objs
}

// An RPC object provides an RPC interface [Genode Book 3.1.1]
sig RPCObject extends GenodeObject {
  owns : one IdentityObject
}

sig PDom {
  objs : set GenodeObject,
  caps : set CapId
} {
  some s : State | this in s.pds // no floating protection domains
  // A capability unambiguously refers to an RPC object [Genode Book 3.1.1]
  some c : caps | some o : RPCObject {
    o.owns = this.cspace.cap_slots[c]
  }
}

pred example {}
run example for 3 but exactly 1 State, exactly 2 PDom, 10 Object,
  exactly 3 RPCObject

pred modifies [s, s' : State, ks, ks' : set KernelObject), ps, ps' : set PDom] {
  s'.kos = (s.kos - ks) + ks'
  s'.pds = (s.pds - ps) + ps'
}

pred PDom.delegate [s, s' : State, r : RPCObject, target : PDom, c : CapId] {
// Preconditions
  this != target // a PDom cannot delegate to itself
  r in this.objs // can only delegate capabilities to an owned RPCObject
  c !in target.@caps // target is given a new capability ID
// Operations
  some target' : s'.pds - (target + this) {
    //let cs = s.cspace_map[target] | s'.cspace_map = (s.cspace_map - {target -> cs}) + {target' -> cs}
    s'.pds = (s.pds - target) + target'
    target'.objs = target.objs
    target'.caps = target.caps + c
    target'.cspace.cap_slots = target.cspace.cap_slots ++ {c -> r.owns}
  }
}

run delegate for 3 but 2 State, 5 Object
