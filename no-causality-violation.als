sig EventId {}

sig Obj {
}


sig Op {
	x: Obj,
	n: Int
}

sig Read,Write extends Op {}



// H is a history event
sig H {
	id: EventId,
	op: Op,
	vis: set H,
	arb: set H
}{
	// event ids are distinct
	all h : H | (h.@id = id) => h = this

	vis in arb
}

sig HEvent {
	x: Obj -> set H
}

sig REvent, WEvent extends HEvent {}

fact ReadsAreReadsAndWritesAreWrites {
	REvent.x[Obj].op in Read
	WEvent.x[Obj].op in Write
}

sig Transaction {
	e : some HEvent,
	po: HEvent -> HEvent
}{
	// po is total
	e in po.e + po[e]

	// po is antisymmetric
	no po & ~po
	
	// po is irreflexive
	no iden & po

	
	// po only contains events from e
	HEvent[po] in e
	HEvent.po in e
}

fact visibilityIsAcyclic {
	all h : H | h not in h.^vis
}

fact arbIsTotalOrder {
	no iden & arb
	no arb & ~arb
	H in arb.H + arb[H]
}

assert noCausalityViolation {
}

pred show() {}

run show for 5
//check noCausalityViolation
