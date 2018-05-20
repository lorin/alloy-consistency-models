---
title: Consistency models
---

# Reading "A Framework for Transactional Consistency Models with Atomic Visibility" with Alloy

[A Framework for Transactional Consistency Models with Atomic Visibility][1] by Cerone, Bernardi and
Gostman uses an axiomatic specification approach to reason about consistency
models of tranactional databases.

This approach lends itself well to modeling with Alloy, so I thought it would
be useful Alloy practice to translate the specifications into Alloy.

Note that this file itself can be loaded directly into Alloy thanks to [Markdown
support in Alloy 5][2].

## Reads and writes

The paper models reads and write operations like this (from Section 2, page
60):

> Op = {read(x, n), write(x, n) | x ∈ Obj, n ∈ Z}

In Alloy:

```alloy
sig Obj {}

abstract sig Op {
	obj: Obj,
	val: Int
}

sig Read,Write extends Op {}
```

Note: we don't really need to model values as integers, but I chose to do it
anyway.

## Event histories

From Section 2, page 60:

> [W]e denote operation invocations using history events of the form (ι, o), where ι is an identifier from a countably infinite
> set EventId and o ∈ Op

In Alloy, we'll call a history event *HEvent*. We'll also distinguish between
reads and writes.

```alloy
sig EventId {}

abstract sig HEvent {
	id: EventId,
	op: Op,
}{
	// event ids are distinct
	all h : HEvent | (h.@id = id) => h = this
}

sig REvent extends HEvent {
}{
	op in Read
}

sig WEvent extends HEvent {
}{
	op in Write
}
```

## Transactions

From Section 2, page 60:

> **Definition 1.** A *transaction* T, S, . . . is a pair (E, po), where E ⊆ HEvent is a finite,
> non-empty set of events with distinct identifiers, and the program order *po* is a total order
> over E.
 
> **Definition 2.** An abstract execution is a triple A = (H, VIS, AR) where:
> - visibility VIS ⊆ H × H is a prefix-finite, acyclic relation; and
> - arbitration AR ⊆ H × H is a prefix-finite, total order such that AR ⊇ VIS.

We'll create a Transaction model in Alloy that captures both definitions.

```alloy
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

	// VIS is a subset of AR
	VIS in AR
}
```


## Repeatable reads 

Here's how the authors *repeatable reads*, from Section 3, p61:

>  if a transaction reads an object twice without writing to it in-between, it will read the same value in both cases.

In Alloy, we can assert all reads are repeatable:

```alloy
assert repeatableReads {
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
```

If we check this assertion, Alloy will find a counterexample:

```alloy
check repeatableReads
```

![repeatable reads counterexample](repeatable-reads.png)

Here are the theme changes I made:

```
EventId -> Show: Off
obj -> Shows as arcs: Off
obj -> Show as attribute: On
val -> Show as arcs: Off
val -> Show as attribute: Off
Obj -> Show: Off
po -> Show as attribute: On
po -> Show as arcs: Off
```

## Internal consistency

If we enforce the *internal consistency axiom*, then this ensures repeatable
reads.



[1]: http://drops.dagstuhl.de/opus/volltexte/2015/5375/pdf/15.pdf 
[2]: https://github.com/AlloyTools/org.alloytools.alloy/wiki/5.0.0-Change-List#markdown-syntax
