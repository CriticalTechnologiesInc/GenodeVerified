module genode

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
  g_objs : PDom lone-> set GenodeObject,
  g_caps : PDom -> set CapId,
  // Genode maintains a one-to-one correspondence between protection domains
  // and CSpaces [assumption]
  cspace_map : PDom one->one CSpace
}

// this kernel object is live in s
pred KernelObject.live [s : State] { this in s.k_objs }

// this Genode object is live in s
pred GenodeObject.live [s : State] { some pd : PDom | this in s.g_objs[pd] }

fun PDom.cspace [s : State] : CSpace { s.cspace_map[this] }

// this protection domain can access o in s using a capability
pred PDom.can_access [s : State, o : RPCObject] {
  o.live[s]
  some c : s.g_caps[this] | {c -> o.owns} in this.cspace[s].cap_slots
}

// A  capability unambiguously refers to an RPC object [Genode Book 3.1.1]
fact {
  all s : State, p : PDom, c : s.g_caps[p] |
    one o : RPCObject | o.owns = s.cspace_map[p].cap_slots[c]
}

// All live identity objects have a live owner, and vice-versa [assumption]
fact {
  all s : State, o : RPCObject, i : IdentityObject |
    o.owns = i => (o.live[s] <=> i.live[s])
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
  let owner = {o : RPCObject | this in o.owns} {
    // Each identity object can have only one owner
    // [implied, Genode Book 3.1.1]
    lone owner
    // Each owned identity object must have an entry reachable from its owner's
    // cspace [assumption]
    all s : State | (one owner && this.live[s]) =>
      (let pd = owner.~(s.g_objs), cs = pd.cspace[s] |
        some c : CapId | {c -> this} in cs.cap_slots)
  }
}

// An RPC object provides an RPC interface [Genode Book 3.1.1]
sig RPCObject extends GenodeObject {
  owns : one IdentityObject
}

pred example {}
run example for 3 but exactly 1 State, exactly 2 PDom, 10 Object

// [Genode Book 3.1.2, first paragraph]
pred RPCObject.delegate [s, s' : State, src, dst : PDom, c : CapId] {
// Preconditions
  this in s.g_objs[src] // can only delegate capabilities to an owned RPCObject
  c !in s.g_caps[dst] // target is given a new capability ID
  //dst.cspace[s].cap_slots[c] = none
// Invariants
  s'.g_objs = s.g_objs
  s'.cspace_map = s.cspace_map
  s'.k_objs = s.k_objs
// Genode Operations
  // add the capability to the target's protection domain
  s'.g_caps = s.g_caps ++ {dst -> {s.g_caps[dst] + c}}
// Kernel Operations
  // add the capability to the target's cspace
  dst.cspace[s'].cap_slots = dst.cspace[s].cap_slots ++ {c -> this.owns}
}

run delegate for 5 but 2 State, exactly 2 PDom // test

delegateOkay : check {
  all s, s' : State, r : RPCObject, src, dst : PDom, c : CapId |
    r.delegate[s, s', src, dst, c] => dst.can_access[s', r]
} for 5 but 2 State

// [Genode Book 3.1.2, last paragraph]
pred RPCObject.destroy [s, s' : State] {
  let pd = this.~(s.g_objs), i = this.owns {
  // Preconditions
    one pd
  // Invariants
    s'.cspace_map = s.cspace_map
  // Genode Operations
    s'.g_objs = s.g_objs - {pd -> this} // destroy the RPC object
    // delete capabilities in this PD for the identity object
    s'.g_caps = s.g_caps :> {c : CapId | pd.cspace[s].cap_slots[c] != i}
  // Kernel Operations
    s'.k_objs = s.k_objs - i // destroy the identity object0
    // remove all cspace references to the identity object
    //all p : PDom | p.cspace[s'].cap_slots = p.cspace[s].cap_slots :> {univ - i}
  }
}

assert live {
  all s, s' : State, r : RPCObject |
    r.destroy[s, s'] => !r.live[s'] && !r.owns.live[s'] && r.live[s] && r.owns.live[s]
}

check live

run destroy for 5 but 2 State // test
