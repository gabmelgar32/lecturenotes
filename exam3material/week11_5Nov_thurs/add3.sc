// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var x: Z = Z.prompt("Enter a positive number: ")

assume(x > 0)


//orig will always be the original user input value
val orig: Z = x

//do we need a proof block here? no, not necessary
Deduce(
    1 ( x > 0 ) by Premise
)


x = x + 1

Deduce(
    1 ( Old(x) > 0 ) by Premise, //from assume
    2 ( x == Old(x) + 1 ) by Premise, //from recent assignment
    3 ( orig == Old(x) ) by Premise, //from previous initialization
    4 ( x == orig + 1 ) by Algebra*(2,3), //summarize change without Old
    5 ( x > 1 ) by Algebra*(1,2) //progress towards 2nd assert
)
//what can we put in a proof block here?
//what should we be able to assert about x and orig?

x = x + 2

Deduce(
    1 ( x == Old(x) + 2 ) by Premise, //from recent assignment
    2 ( Old(x) == orig + 1 ) by Premise, //shown in previous proof block
    3 ( x == orig + 3 ) by Algebra*(1,2), //proves 1st assert
    4 ( Old(x) > 1 ) by Premise, //shown in previous block
    5 ( x > 3 ) by Algebra*(1, 4) //proves 2nd assert

    //need to show that x > 3
)

//what do we want to assert? How has x changed?
assert(x == orig + 3)
assert(x > 3)


//Once it is working - if x was originally positive,
//how could we assert that x was still positive at the end?