module genode

// Represents a protection domain
sig PDom {}

// Represents a capability identifier (e.g. an integer)
sig CapId {}

abstract sig Object {}
abstract sig GenodeObject extends Object {}
sig KernelObject extends Object {}
// CSpace contains a finite number of slots, each of which may contain a
// capability [Genode Book 3.1.1]
sig CSpace extends KernelObject {}

// An RPC object provides an RPC interface [Genode Book 3.1.1]
sig RPCObject extends GenodeObject {
  owns : one IdentityObject
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
      (let pd = owner.~(s.g_objs), cs = pd.cspace |
        some c : CapId | {c -> this} in s.cap_slots[cs])
  }
}

// Immutable state
one sig ImmutState {
  // Genode maintains a one-to-one correspondence between protection domains
  // and CSpaces [assumption]
  cspace_map : PDom one->one CSpace
}
fun cs_map : PDom -> CSpace { {is : ImmutState}.cspace_map }

// Note that this combines Genode's state AND the kernel state
sig State {
  k_objs : set KernelObject,
  // genode objects are not shared between protection domains [assumption]
  g_objs : PDom lone-> set GenodeObject,
  g_caps : PDom -> set CapId,
  // this simple model assumes CSpaces are non-recursive (not the case in seL4)
  // [assumption]
  cap_slots : CSpace -> (CapId ->lone (KernelObject - CSpace))
} {
  all pd : PDom, cs : CSpace | {pd -> cs} in cs_map => cs.live[this]
}

// this kernel object is live in s
pred KernelObject.live [s : State] { this in s.k_objs }
// this Genode object is live in s
pred GenodeObject.live [s : State] { some pd : PDom | this in s.g_objs[pd] }

fun PDom.cspace : CSpace { {s : ImmutState}.cspace_map[this] }

// this protection domain can access o in s using a capability
pred PDom.can_access [s : State, o : RPCObject] {
  o.live[s]
  some c : s.g_caps[this] | {c -> o.owns} in s.cap_slots[this.cspace]
}

// A  capability unambiguously refers to an RPC object [Genode Book 3.1.1]
fact {
  all s : State, p : PDom, c : s.g_caps[p] |
    one o : RPCObject | o.owns = s.cap_slots[p.cspace][c]
}
// All live identity objects have a live owner, and vice-versa [assumption]
fact {
  all s : State, o : RPCObject, i : IdentityObject |
    o.owns = i => (o.live[s] <=> i.live[s])
}
// All capabilities in cap slots refer to live kernel objects [assumption]
fact {
  all s : State, cs : CSpace, c : CapId, k : KernelObject |
    cs.live[s] => {c -> k} in s.cap_slots[cs] => k.live[s]
}

pred example {}
run example for 3 but exactly 1 State, exactly 2 PDom, 10 Object

// [Genode Book 3.1.2, first paragraph]
pred RPCObject.delegate [s, s' : State, src, dst : PDom, c : CapId] {
// Preconditions
  this in s.g_objs[src] // can only delegate capabilities to an owned RPCObject
  c !in s.g_caps[dst] // target is given a new capability ID
// Invariants
  s'.g_objs = s.g_objs
  s'.k_objs = s.k_objs
// Genode Operations
  // add the capability to the target's protection domain
  s'.g_caps = s.g_caps ++ {dst -> {s.g_caps[dst] + c}}
// Kernel Operations
  // add the capability to the target's cspace
  let cs = dst.cspace, slots = s.cap_slots[cs] |
    s'.cap_slots = s.cap_slots ++ {cs -> (slots ++ {c -> this.owns})}
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
  // Genode Operations
    s'.g_objs = s.g_objs - {pd -> this} // destroy the RPC object
    // delete capabilities in this PD for the identity object
    s'.g_caps = s.g_caps :> {c : CapId | s.cap_slots[pd.cspace][c] != i}
  // Kernel Operations
    s'.k_objs = s.k_objs - i // destroy the identity object0
    // remove all cspace references to the identity object
    all p : PDom | s'.cap_slots[p.cspace] = s.cap_slots[p.cspace] :> {univ - i}
  }
}

run destroy for 5 but 2 State // test

destroyOkay : check {
  all s, s' : State, r : RPCObject |
    r.destroy[s, s'] => (all pd : PDom | !pd.can_access[s', r])
} for 5 but 2 State
