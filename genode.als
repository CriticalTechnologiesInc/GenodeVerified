module genode

// FIXME: A capability unambiguously refers to an RPC object [Genode Book 3.1.1]

// Represents a protection domain
sig PDom {}

abstract sig Object {}
abstract sig GenodeObject extends Object {}
sig KernelObject extends Object {}

// Represents a capability identifier (e.g. an integer)
sig CapId {}

// Note that this combines Genode's state AND the kernel state
sig State {
  k_objs : set KernelObject,
  // genode objects are not shared between protection domains [assumption]
  g_objs : PDom one-> set GenodeObject,
  g_caps : PDom -> set CapId,
  // Genode maintains a one-to-one correspondence between protection domains
  // and CSpaces [assumption]
  cspace_map : PDom one->one CSpace
}

// this kernel object is live in s
pred KernelObject.live [s : State] { this in s.k_objs }

// this Genode object is live in s
pred GenodeObject.live [s : State] { some this.~(s.g_objs) }

// this protection domain can access k in s using a capability
pred PDom.can_access [s : State, k : KernelObject] {
  some c : s.g_caps[this] | {c -> k} in s.cspace_map[this].cap_slots
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
  all s : State | let owner = {o : RPCObject | this in o.owns[s]} {
    // Each identity object can have only one owner
    // [implied, Genode Book 3.1.1]
    lone owner
    // Each owned identity object must have an entry reachable from its owner's
    // cspace [assumption]
    one owner <=> this.live[s] &&
      (let pd = owner.~(s.g_objs) | pd.can_access[s, this])
  }
}

// An RPC object provides an RPC interface [Genode Book 3.1.1]
sig RPCObject extends GenodeObject {
  owns : State ->one IdentityObject
}

pred example {}
run example for 3 but exactly 1 State, exactly 2 PDom, 10 Object,
  exactly 3 RPCObject

/*pred modifies [s, s' : State, ks, ks' : set KernelObject, ps, ps' : set PDom] {
  s'.kos = (s.kos - ks) + ks'
  s'.pds = (s.pds - ps) + ps'
}*/

/*pred PDom.delegate [s, s' : State, r : RPCObject, target : PDom, c : CapId] {
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

run delegate for 3 but 2 State, 5 Object*/
