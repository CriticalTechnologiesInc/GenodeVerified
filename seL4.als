module seL4

/* This module follows the seL4 specification v1.3 */

/* 
 * Some general design principles to follow:
 * - Immutable objects contain their state within their sig, otherwise state
 *   should be provided in the State sig
 * - Enum-style declarations should be laid out like, e.g. AccessRight
 * - ALWAYS cite our assumptions from text, source code, etc. The more the
 *   better!
*/

// [S. 14, p. 67]
abstract sig AccessRight {}
one sig AllowRead extends AccessRight {}
one sig AllowWrite extends AccessRight {}
one sig AllowGrant extends AccessRight {}

// [S. 18.2, p. 89]
abstract sig StateEP {}
one sig SendEP extends StateEP {}
one sig RecvEP extends StateEP {}

sig CNodeIndex {}

sig KernelObject {}
sig Endpoint extends KernelObject {}
sig TCB extends KernelObject {
  // The root CNode (forms the CSpace) is immutable [assumption]
  ctable : one CNodeCap
}
sig CNode extends KernelObject {}

// [S. 18, p. 85-86] We assume capabilities are immutable
abstract sig Cap {}
sig EndpointCap extends Cap {
  obj_ref : one Endpoint, // we're assuming type safety here
  cap_rights : set AccessRight
}
sig CNodeCap extends Cap {
  obj_ref : one CNode
}

sig State {
  // [S. 18.2, p. 88] An endpoint is idle when its set of TCBs is empty
  ep_state : Endpoint ->one StateEP,
  ep_waiting : Endpoint lone->set TCB, // each TCB can wait on only 1 endpoint
  // [S. 18, p. 86]
  cnode_map : CNode -> (CNodeIndex ->lone Cap),
  // [S. 18.3, p. 91] mapping from capabilities to parents
  cdt : (CNode -> CNodeIndex) ->lone (CNode -> CNodeIndex)
} {
  // CNode slots in the CDT must be non-empty (assumption)
  all cn, cn' : CNode, i, i' : CNodeIndex |
    ({cn -> i} -> {cn' -> i'}) in cdt
       => some cnode_map[cn][i] && some cnode_map[cn'][i]
}

pred example {
  all c : EndpointCap | AllowRead !in c.cap_rights && AllowWrite in c.cap_rights
}
run example for 5 but exactly 1 State, exactly 2 TCB, exactly 3 EndpointCap

// Returns the set of CNodes reachable from this CNode in 's' (non-reflexive)
fun CNode.reachable [s : State] : set CNode {
  let trans = {cn, cn' : CNode
    | some i : CNodeIndex | let c' = s.cnode_map[cn][i]
    | c' in CNodeCap && c'.obj_ref = cn'}
  | {cnode : CNode | cnode in this.^trans}
}

// [CITEME]
fact CNode_Acyclic { all s : State, cn : CNode | cn !in cn.reachable[s] }

// Whether 'c' is derived from this Cap in the CDT (non-reflexive)
pred Cap.derived_from [s : State, c : Cap] {
  let trans = {ca, ca' : Cap | some cn, cn' : CNode, i, i' : CNodeIndex |
    ca = s.cnode_map[cn][i] && ca' = s.cnode_map[cn'][i'] &&
    s.cdt[cn][i] = {cn' -> i'}}
  | c in this.^trans
}

// [CITEME]
fact CDT_Acyclic { all s : State, c : Cap | not c.derived_from[s, c] }

// set of Caps possessed by this TCB
fun TCB.caps[s : State] : set Cap {
  this.ctable +
    {c : Cap | some i : CNodeIndex, cn : this.ctable.obj_ref.reachable[s]
               | {i -> c} in s.cnode_map[cn]}
}

pred TCB.possesses_cap_to_object[s : State, k : KernelObject] {
  some c : this.caps[s] |
    // NOTE: This must enumerate all subtypes of Cap!
    (c in EndpointCap => some c.cap_rights => k = c.(EndpointCap<:obj_ref)) &&
    (c in CNodeCap => k = c.(CNodeCap<:obj_ref))
}

pred example1 {
  some t : TCB, s : State, e : Endpoint | t.possesses_cap_to_object[s, e]
}
run example1 for 5 but exactly 1 State, 2 CNodeIndex
