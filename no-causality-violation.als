sig EventId {}

sig Obj {
}

sig Op {
	x: Obj,
	n: Int
}

sig Read,Write extends Op {}

sig HEvent {
	id: EventId,
	op: Op,
}{
	// event ids are distinct
	all h : HEvent | (h.@id = id) => h = this
}


sig REvent, WEvent extends HEvent {}

fact ReadsAreReadsAndWritesAreWrites {
	REvent.op in Read
	WEvent.op in Write
}

fact OnlyReadsAndWrites {
	HEvent in REvent + WEvent
}

sig Transaction {
	e : some HEvent,
	po: HEvent -> HEvent,
	vis: set Transaction,
	arb: set Transaction
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

	// vis is a subset of arb
	vis in arb
}

fact visibilityIsAcyclic {
	all t : Transaction | t not in t.^vis
}

fact arbIsTotalOrder {
	no iden & arb
	no arb & ~arb
	Transaction in arb.Transaction + arb[Transaction]
}

// To reduce orphaned object
fact AllOpsAreAssociatedWithHistoryEvents {
	Op in HEvent.op
}

fact AllObjectsAreAssociatedWithOperations {
	Obj in Op.x
}


/*
If a transaction reads an object twice without writing to it in-between,
it will read the same value in both cases
*/
assert noUnrepeatableReads {
all t : Transaction | 
	all r1,r2 : t.e & REvent |
		// if same object is being read and r1 comes before r2
		(r1.op.x = r2.op.x and r1->r2 in t.po 
			// and no write after r1 and before r2
			and no w : t.e & WEvent | w.op.x = r1.op.x and ({r1->w} + {w->r2}) in t.po) =>
		// then they will read the same value
		r1.op.n = r2.op.n
}

pred show() {}

//run show for 5
check noUnrepeatableReads
