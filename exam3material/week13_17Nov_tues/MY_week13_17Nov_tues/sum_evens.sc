// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(n >= 0), // the precondition
    Ensures(Res[Z] == n*(n+1)) 
  )

  var sum: Z = 0
  var cur: Z = 0

  //must prove invariant befoer loop begins
  Deduce(
    1(sum == 0) by Premise,
    2(cur == 0) by Premise,
    3(sum == cur*(cur+1)) by Algebra*(1,2)// proves the invariant
  )

  while (cur != n) {
    //what about our loop invariant?
    Invariant(
      Modifies(cur,sum),
      sum == cur*(cur+1)
    )
    cur = cur + 1

    //process variable change
    //anything from before the loop is not fair game, not true at the beginning of each iteration
    Deduce(
      1(cur == Old(cur)+ 1) by Premise, //from assignment
      2(Old(cur)!= n) by Premise,
      3(Old(cur) == cur -1) by Algebra*(1),
      4(sum == Old(cur)*(Old(cur)+1)) by Premise, //invariant was true
      5(sum == (cur -1)*((cur - 1)+1)) by Algebra*(3,4) //process 

    )


    sum = sum + 2*cur

    //prove the invariant still holds here
    Deduce(
      1(Old(sum)== (cur-1)*((cur-1)+1)) by Premise,
      2(sum == Old(sum) + 2*cur) by Premise,
      3(sum == (cur-1)*((cur-1)+1) + 2*cur ) by Algebra*(1,2),
      4(sum == (cur-1)*cur + 2*cur) by Algebra*(3),
      5(sum == cur*cur - cur + 2*cur) by Algebra*(4),
      6(sum == cur*cur + cur) by Algebra*(5),
      7(sum == cur*(cur+1)) by Algebra*(6) //proves invariant
    )

  }

Deduce(
  1(!(cur!=n) ) by Premise,
  2(cur == n) by Algebra*(1),
  3(sum == cur*(cur+1)) by Premise,
  4(sum == n*(n+1)) by Algebra*(2,3)
)

  return sum
}

//////////// test code /////////

val num: Z = 5

//prove its precondition
Deduce(
  1(num == 5) by Premise,
  2(num >= 0) by Algebra*(1)
)

var sum5evens: Z = sumEvens(num)

Deduce(
  1(sum5evens == num*(num+1)) by Premise,
  2(num == 5) by Premise,
  3(sum5evens == 30) by Algebra*(1,2)
)

//sum of first 5 evens: ?
assert(sum5evens == 30)