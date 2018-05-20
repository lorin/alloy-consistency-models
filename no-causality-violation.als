sig EventId {}

sig Obj {
}

sig Op {
	obj: Obj,
	val: Int
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
	Op in Read + Write
}

sig Transaction {
	E : some HEvent,
	po: HEvent -> HEvent,
	VIS: set Transaction,
	AR: set Transaction
}{
	// po is total
	all e1, e2 : E | e1!=e2 => (e1->e2 in po or e2->e1 in po)

	// po is antisymmetric
	no po & ~po
	
	// po is irreflexive
	no iden & po

	// po only contains events from e
	po in E->E

	// vis is a subset of ar
	VIS in AR
}

fun max[R : HEvent->HEvent, A : set HEvent] : HEvent {
	// the element u \in A s.t.
	// all v in A. v = u or (v,u) in R
	{u : A | all v : A | v=u or v->u in R }
}

fun min[R : HEvent->HEvent, A : set HEvent] : HEvent {
	{u : A | all v : A | v=u or u->v in R }
}


fun HEventObj[x : Obj] : HEvent {
	{e : HEvent | e.op.obj = x }
}

fun WEventObj[x : Obj] : WEvent {
	HEventObj[x] & WEvent
}

// In transaction t, the last write to object x was value n
pred TWrites[t : Transaction, x : Obj, n : Int] {
	let lastWriteX = max[t.po, t.E & WEventObj[x]].op |
		lastWriteX in Write and lastWriteX.obj=x and lastWriteX.val=n
}

// In transaction t, the first access to object x was a read of value n
pred TReads[t : Transaction, x : Obj, n : Int] {
	let firstOpX = min[t.po, t.E & HEventObj[x]].op |
		firstOpX in Read and firstOpX.obj=x and firstOpX.val=n
}

fun maxAR[T: set Transaction] : Transaction {
	{t : T | all s : T | s=t or s->t in AR}
	
}

fact INT {
	all t : Transaction |
		all e : t.E |
			all x : Obj |
				all n : Int |
					let maxE = max[t.po, ~(t.po).e & HEventObj[x]] | 
						(e.op in Read and e.op.obj=x and e.op.val=n and x in (~(t.po).e).op.obj)
						=> (maxE.op.obj=x and maxE.op.val=n)
}

fact EXT {
	all t : Transaction |
		all x : Obj |
			all n : Int |
				TReads[t, x, n] => 
					let WritesX = {s : Transaction | (some m : Int | TWrites[s, x, m]) } |
					(no (VIS.t & WritesX) and n=0) or TWrites[(maxAR[VIS.t & WritesX]), x, n]
}


fact eventsBelongToExactlyOneTransaction {
	all ev : HEvent | #(E.ev)=1
}


fact visibilityIsAcyclic {
	all t : Transaction | t not in t.^VIS
}


fact ArIsTotalOrder {
	no (iden & AR)
	no (AR & ~AR)
	all t1, t2 : Transaction | t1!=t2 => t1->t2 in AR or t2->t1 in AR
}

// To reduce orphaned object
fact AllOpsAreAssociatedWithHistoryEvents {
	Op in HEvent.op
}

fact AllObjectsAreAssociatedWithOperations {
	Obj in Op.obj
}


/*
If a transaction reads an object twice without writing to it in-between,
it will read the same value in both cases
*/
assert noUnrepeatableReads {
all t : Transaction | 
	all r1,r2 : t.E & REvent |
		// if same object is being read and r1 comes before r2
		((r1.op.obj = r2.op.obj) and 
     (r1->r2 in t.po) and
			// and no write after r1 and before r2
		 (no w : t.E & WEvent | (w.op.obj = r1.op.obj and ({r1->w} + {w->r2}) in t.po)))
		// then they will read the same value
		=> 	r1.op.val = r2.op.val
}

pred show() {
	some Read
	some Write
	#Transaction > 1
}

run show 
// check firstReadMustReadZero

// check noUnrepeatableReads
