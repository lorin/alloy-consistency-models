sig EventId {}
sig Op {}

sig HistoryEvent {
	id: EventId,
	op: Op
}{
	// event ids are unique
	all h : HistoryEvent | (h.@id = id) => h = this
}

assert noCausalityViolation {
}

pred show() {}

run show

//check noCausalityViolation
