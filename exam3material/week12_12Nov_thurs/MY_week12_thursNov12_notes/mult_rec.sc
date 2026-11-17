// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    //what do we need to do here?
  } else {

    var temp: Z = mult(x, y-1)
    answer = x + temp

    Deduce(
      1 ( answer == x + temp ) by Premise, //from assignment
      2 ( !(y == 0) ) by Premise, //if condition is false (not needed here)
      3 ( temp == x*(y-1)  ) by Premise, //from postcondition after recursive call

      4 ( temp == x*y - x ) by Algebra*(3),
      5 ( answer == x + x*y - x ) by Algebra*(1,4),
      6 ( answer == x*y ) by Algebra*(5) //proves postcondition for else
    )

    Deduce(
      1(answer == x + temp) by Premise, //from assignment
      2(!(y == 0) ) by Premise, // if conditon is false(not needed here)
      3(temp == x *(y-1)) by Premise, //from postconditon after recursive call

      4(temp == x*y - x) by Algebra*(3),//this step is not needed but helpful to show what is happening
      5(answer == x + x*y - x) by Algebra*(1,4), // this step is not needed but helpful to show what is happening 
      6(answer == x*y) by Algebra*(5) //proves post conditon for else
    )
    //what do we need to show here?
  }

  Deduce(
    1 ( answer == x*y ) by Premise
  )

  //what do we need to do here?

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

var ans: Z = mult(a, b)

//prove the assert
Deduce(
  1 ( a == 5 ) by Premise, //from assignment
  2 ( b == 4 ) by Premise, //from assignment
  3 ( ans == a*b ) by Premise, //from postcondition
  4 ( ans == 20 ) by Algebra*(1,2,3) //proves assert

  //need: ans == 20
)

//what do we want to assert that ans is?