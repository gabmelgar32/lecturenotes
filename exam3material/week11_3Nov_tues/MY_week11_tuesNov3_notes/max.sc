// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = Z.prompt("Enter first number: ")
val y: Z = Z.prompt("Enter second number: ")

//x = 3, y = 4

//how do we assume x is bigger than y?
assume(x > y)

val max: Z = x


assert(max >= x (and symbol) max >= y)
assert(max == x | max == y)
//what can we put in a proof block here?

//how do we assert max is the biggest between our two inputs?
