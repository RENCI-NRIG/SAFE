package prolog.terms
import prolog.builtins.true_

final class Answer(x: Term) extends Fun("return", Array(x)) {
  override def safeCopy(): Fun = {
    new Answer(null)
  }
}
