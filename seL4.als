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
one sig AllowRead in AccessRight {}
one sig AllowWrite in AccessRight {}
one sig AllowGrant in AccessRight {}

// [S. 18.2, p. 89]
abstract sig StateEP {}
one sig SendEP in StateEP {}
one sig RecvEP in StateEP {}

sig KernelObject {}
sig Endpoint extends KernelObject {}
sig TCB extends KernelObject {}

// [S. 18, p. 85-86] We assume capabilities are immutable
abstract sig Cap {}
sig EndpointCap extends Cap {
  obj_ref : one Endpoint, // we're assuming type safety here
  cap_rights : set AccessRight
}

sig State {
  // [S. 18.2, p. 18] An endpoint is idle when its set of TCBs is empty
  ep_state : Endpoint one-> (StateEP one->set TCB)
}
