package projectname

import spinal.core._
import scala.collection.mutable.Queue

object ImperativeHighLevelSpecInScalaForNoReason {
  case class Input[V](uValid: Boolean, uData: V, dReady: Boolean)
  case class Output[V >: Null](var dValid: Boolean = false, var dData: V = null, var uReady: Boolean = false)
  case class SkidBuffer[V >: Null]() {
    val CAPACITY = 2
    val q: Queue[V] = Queue.empty
    def step(in: Input[V]): Output[V] = {
      val out = Output[V]()
      out.dValid = (q.size > 0)
      out.uReady = (q.size < CAPACITY)
      if (out.dValid) {
        out.dData = q.front
        if (in.dReady) {
          q.dequeue()
        }
      }
      if (out.uReady && in.uValid) {
        q.enqueue(in.uData)
      }
      out
    }
  }

}
