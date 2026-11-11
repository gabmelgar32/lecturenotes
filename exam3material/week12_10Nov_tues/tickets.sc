// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//adult tickets: $50
//kid tickets: $30
def getTicketCosts(adult: Z, kid: Z): Z = {
  //what do we want for our function contract?
  Contract(
    Requires(adult >= 0, kid >= 0),
    Ensures(Res[Z] == adult*50 + kid*30, Res[Z] >= 0)
  )


  //get the total ticket cost
  val overall: Z = adult*50 + kid*30

  //what to do here? need to prove the postconditions
  Deduce(
    //need: overall == adult*50 + kid*30
    //need: overall >= 0
    1 ( overall == adult*50 + kid*30 ) by Premise, //from assignment, proves 1st postcondition
    //can list all preconditions as premises
    2 ( adult >= 0 ) by Premise, //from precondition
    3 ( kid >= 0 ) by Premise, //from precondition
    4 ( overall >= 0 ) by Algebra*(1,2,3) //proves postcondition
  )

  return overall
}

////////////// Test code /////////////////

val k: Z = 3 //$30 each
val a: Z = 2 //$50 each

//what to do here?
//need to prove the preconditions (requires) about what is being passed
//prove a >= 0, k >= 0
Deduce(
  1 ( k == 3 ) by Premise, //from assignment
  2 ( a == 2 ) by Premise, //from assignment
  3 ( a >= 0 ) by Algebra*(2), //proves 1st precondition
  4 ( k >= 0 ) by Algebra*(1) //prove 2nd precondition
)

val cost: Z = getTicketCosts(a, k)

//what to do here?
//need: cost == 190

//can list all postconditions as premises
Deduce(
  1 ( cost == a*50 + k*30 ) by Premise, //from postcondition
  2 ( cost >= 0 ) by Premise, //from 2nd postcondition
  3 ( a == 2 ) by Premise,
  4 ( k == 3 ) by Premise,
  5 ( cost == 190 ) by Algebra*(1,3,4)
)


//what *should* cost be?
assert(cost == 190)