package typingExamplesUnstV

import reflect.Selectable.reflectiveSelectable

import typing_unstamped_derivedV._
import scalaLibV._

/* We only show here the hashKeys example from the source file.
 */

/**
  First example from "The Essence of Dependent Object Types". Original code:
*/

trait Keys {
  type Key
  val key : HashableString => Key
}

object HashKeys extends Keys {
  type Key = Int
  val key = s => s.hashCode_()
}

//  Note we upcast Int to this.Key; as expected, no later is needed.
