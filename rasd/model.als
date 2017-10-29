module travlendar

open util/integer
open util/ordering[Calendar] as calOrdering

/*
Notes about our model:
It tries to verify the objectives described below.
Only entities and properties relevant to the formal model are considered here: 
it doesn't make sense to say that an event has a name for formal purposes.

There's one calendar (which evolves), and one user. This is reasonable because 
a user's calendar is writable only by that user.

Objectives:
 - if the user inserts an event which overlaps with another a warning is generated
 - if an event is inserted and there's no way to reach the destination in time a 
 	warning is generated
 - if the user inserts an event which leaves no time for flexible events a 
 	warning is generated
*/

// --------------------- SIGNATURES ---------------------
sig Calendar {
	events: set Event,
	eventsWithOverlaps: set Event,
	unreachableEvents: set Event
}

sig Event {
	travelTime: Int,
	starting: Int,
	ending: Int
} { starting < ending && travelTime >= 0 && starting >= 0 && ending > 0 }

// --------------------- FACTS ---------------------
fact {
	emptyCalendar[calOrdering/first]
}

// --------------------- DYNAMIC BEHAVIOR ---------------------
// these predicates represent operations on the dynamic system

// Adds an event to a calendar
pred addEventToCalendarPrecondition[e: Event, c: Calendar] {
	e not in c.events
}

pred addEventToCalendar[e: Event, c, c': Calendar] {
	addEventToCalendarPrecondition[e, c] => 
		c'.events = c.events + e
	else c' = c
	
	addEventToCalendarPrecondition[e, c] &&
	overlapsWithOtherEvents[e, c] => 
		c'.eventsWithOverlaps = c.eventsWithOverlaps + e + 
								{ e2 : c.events | twoEventsOverlap[e, e2] }
	else c.eventsWithOverlaps = c'.eventsWithOverlaps

	addEventToCalendarPrecondition[e, c] &&
	unreachableInTime[e, c] => 
		c'.unreachableEvents = c.unreachableEvents + e
	else c'.unreachableEvents = c.unreachableEvents
}

// Removes an event from a calendar
pred removeEventFromCalendarPrecondition[e: Event, c: Calendar] {
	e in c.events
}
pred removeEventFromCalendar[e: Event, c, c': Calendar] {
	removeEventFromCalendarPrecondition[e, c] =>
		c'.events = c.events - e &&
		c'.unreachableEvents = c.unreachableEvents - e &&
		c'.eventsWithOverlaps = c.eventsWithOverlaps - 
								{ e2 : c.events | twoEventsOverlap[e, e2] }
	else c' = c
}

// --------------------- HELPERS ---------------------

pred emptyCalendar [c: Calendar] {
	no c.events && no c.eventsWithOverlaps && no c.unreachableEvents
}

// Evaluates whether there's another overlapping event in the calendar
pred overlapsWithOtherEvents[e: Event, c: Calendar] {
	! (no e2: c.events | e != e2 && twoEventsOverlap[e, e2])
}

// Evaluates whether two events overlap
pred twoEventsOverlap[e1, e2: Event] {
	e1.starting < e2.ending && e1.ending > e2.starting && e1 != e2
}

fun precedingEvents[e: Event, c: Calendar] : set Event {
	{ e': c.events | e'.ending <= e.starting }
}

// Evaluates whether an event is unreachable in time
pred unreachableInTime[e: Event, c: Calendar] {
	! (no e' : precedingEvents[e, c] | 
		e'.ending + e.travelTime > e.starting
	)
}

// --------------------- ASSERTIONS ---------------------

// Asserts that if two overlapping events are added 
// a warning associated with them is generated
assert addingOverlappingEventsGeneratesWarning {
	all c, c', c'': Calendar, disj e1, e2: Event |
		// When adding two overlapping events
		e1 != e2 &&
		twoEventsOverlap[e1, e2] && 
		addEventToCalendarPrecondition[e1, c] &&
		addEventToCalendar[e1, c, c'] && 
		addEventToCalendarPrecondition[e2, c'] &&
		addEventToCalendar[e2, c', c''] =>

		// a warning is generated for the overlapping events
		(e1 + e2) in c''.eventsWithOverlaps
}

assert addEventToCalendarAddsEvent {
	all c, c': Calendar, e: Event | 
		addEventToCalendarPrecondition[e, c] &&
		addEventToCalendar[e, c, c'] => e in c'.events
}

assert addingUnreachableEventGeneratesWarning {
	all c, c': Calendar, e: Event | 
		unreachableInTime[e, c] &&
		addEventToCalendarPrecondition[e, c] &&
		addEventToCalendar[e, c, c'] =>
		e in c'.unreachableEvents
}

assert removeUndoesAdd {
	all c, c', c'': Calendar, e: Event |
		addEventToCalendarPrecondition[e, c] &&
		addEventToCalendar[e, c, c'] &&
		removeEventFromCalendarPrecondition[e, c'] &&
		removeEventFromCalendar[e, c', c''] => c = c''
}


// --------------------- CHECKS ---------------------

/* Check ok
check twoEventsOverlapSanity {
	all e1, e2: Event |
	twoEventsOverlap[e1, e2] <=> twoEventsOverlap[e2, e1]
}
*/

// works, no counterexamples found
// check addingOverlappingEventsGeneratesWarning for 10 expect 0
// works, no counterexamples found
// check addEventToCalendarAddsEvent expect 0
// check removeUndoesAdd for 3
// works, no counterexamples found
// check addingUnreachableEventGeneratesWarning expect 0

	








