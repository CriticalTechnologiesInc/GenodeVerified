module sel4_integrity

abstract sig Auth{}
one sig Receive extends Auth{}
one sig SyncSend extends Auth{}
one sig AsyncSend extends Auth{}
one sig Reset extends Auth{}
one sig Grant extends Auth{}
one sig Write extends Auth{}
one sig Read extends Auth{}
one sig Control extends Auth{}

abstract sig L{}
one sig UT1 extends L {}
one sig UT2 extends L {}
one sig T1 extends L {}
one sig T2 extends L {}

sig PAS{
	pasPolicy: L -> Auth -> L,
	pasObjectAbs : obj_ref -> L,\
	pasSubject : one L
}

pred policy_wellformed[policy: L -> Auth -> L, subject: L]{
	all a:L | (subject -> Control -> a)  in policy => subject = a
	all a:Auth | (subject -> a ->subject) in policy
	// Grant restriction left out
}

abstract sig KernelObject{
	auth : Auth -> obj_ref 
}

sig Capability{}
//sel4-refman.pdf p7  5, sel4_specification.pdf p72
sig TCB extends KernelObject{
	tcb_ctable: one Capability,
	tcb_vtable : one Capability
}

sig obj_ref{}

sig State{
	kheap : obj_ref -> lone KernelObject 
}

pred pas_refined[p:PAS, s:State]{
	policy_wellformed [p.pasPolicy, p.pasSubject]
	//auth_graph_map [p.pasObjectAbs,state_objs_to_policy s] in p.pasPolicy	
	all obj1: obj_ref, a: Auth,  obj2: a.((obj1.(s.kheap)).auth) | 
		obj1.(p.pasObjectAbs) -> a -> obj2.(p.pasObjectAbs) in p.pasPolicy
	//stuff left out
}

fact scope{
	#obj_ref <= 10
	#State <= 2
	#TCB <= 3
}
pred unconstrained{}
pred eg{
	some p:PAS, s:State | pas_refined[p,s]
}
run eg


