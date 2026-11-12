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
  Contract(
    Requires(y >= 0), //because our condition is y ==0, we want our else to be greater than 0 otherwise it will get infinitely smaller
    Ensures(Res[Z] == x * y)
  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    Deduce(
      1(y == 0) by Premise, //if ocndition is true
      2(answer == 0) by Premise, //from assignment
      3(y > 0) by Premise, //from pre conditon but not needed s
      4(answer == x * y ) by Algebra*(1,2) // proves postcondition 
    )

    //what do we need to do here?
    //we need answer == x*y here as well
  } else {

    //need to prove precondition(requires) before recursive call
    Deduce(
      //need to prove: y - 1 >= 0
      1(y >= 0) by Premise, //precondition
      2(!(y == 0)) by Premise,
      3(y-1 >= 0) by Algebra*(1,2) //this proves precondition

    )

    //this tells me x*(y-1)
    //will be x + x + x a total of y-1 times
    var temp: Z = mult(x, y-1)
    answer = x + temp

    Deduce(
      1(answer == x + temp) by Premise, //from assignment
      2(!(y == 0) ) by Premise, // if conditon is false(not needed here)
      3(temp == x *(y-1)) by Premise, //from postconditon after recursive call

      4(temp == x*y - x) by Algebra*(3),//this step is not needed but helpful to show what is happening
      5(answer == x + x*y - x) by Algebra*(1,4), // this step is not needed but helpful to show what is happening 
      6(answer == x*y) by Algebra*(5) //proves post conditon for else
    )
    //what do we need to show here?
    //we need answer == x*y here 
  }

  //what do we need to do here?
  //we need to prove our post condition
  //this is the post condition: Ensures(Res[Z] == x * y) 

  Deduce(
    1(answer == x * y) by Premise
  )

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

//prove the preconditon before the call
Deduce(
  1(b == 4) by Premise,
  2(b >= 0) by Algebra*(1)//proves preconditon

  //need to prove b >=0 
)

var ans: Z = mult(a, b)

Deduce(
  1(a == 5) by Premise, //from assignment
  2(b == 4) by Premise, //from assignment
  3(ans == a*b) by Premise, //from postcondition
  4(ans == 20) by Algebra*(1,2,3) //proves the assert
  
  //need answer == 20
)

//what do we want to assert that ans is? -- we should be wanting to assert 20
assert(ans == 20)

//we want to prove our pre condition in each branch 