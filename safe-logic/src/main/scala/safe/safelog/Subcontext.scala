package safe.safelog

import scala.collection.mutable.{LinkedHashSet => OrderedSet}
import scala.collection.mutable.{Map => MutableMap}
import org.joda.time.DateTime

case class Subcontext(
  val id: SetId,
  var freshUntil: Option[DateTime],
  var refreshableUntil: Option[DateTime],
  var slogsetTokens: OrderedSet[String],
  val facts: MutableMap[Index, OrderedSet[Statement]],
  val rules: MutableMap[Index, OrderedSet[Statement]],
  val queries: OrderedSet[Statement]
) {

  def expired(): Boolean = {
    val now = new DateTime()
    val res = freshUntil.isDefined && freshUntil.get.isBefore(now)
    res
  }

  def isSlangSubcontext(): Boolean = {
    return id.name.equals("_object")
  }

  def setRefreshableUntil(refreshable: DateTime): Option[DateTime] = {
    refreshableUntil = Some(refreshable)
    refreshableUntil
  }

  /**
   * Update freshUntil
   * Bump freshUtil if the new expiration comes earlier
   * Called when adding a slogset into the Subcontext
   */
  def updateFreshUntil(expiration: DateTime): Option[DateTime] = {
    if(!freshUntil.isDefined || freshUntil.get.isAfter(expiration)) {
      freshUntil = Some(expiration) 
    }
    freshUntil
  } 

  /**
   * Keep track of the set tokens in a subcontext
   * Called when adding a slogset into the subcontext
   */
  def addSetToken(token: String): Unit = {
    slogsetTokens += token
  }

  /**
   * Add statements into the Subcontext
   */
  def addStatements(stmts: Map[Index, OrderedSet[Statement]]): Unit = {
    for(index <- stmts.keySet) {
      val stmtSet: OrderedSet[Statement] = stmts(index)
      for(stmt <- stmtSet) {
        if(stmt.isFact) { // Index into facts
          //println(s"Indexing fact     index: ${index}    stmt: ${stmt}")
          indexStmt(facts, index, stmt)   // TODO: add the secondary index for the fact as well
        } else { // Index into rules
          //println(s"Indexing rule     index: ${index}    stmt: ${stmt}")
          indexStmt(rules, index, stmt) 
        }
      }
    } 
  }

  private def indexStmt(stmtsMap: MutableMap[Index, OrderedSet[Statement]], 
      index: Index, stmt: Statement): Unit = { 
    if(index.name == RETRACTION_INDEX || index.name == LINK_INDEX) return
    stmtsMap.get(index) match {
      case Some(stmtSet: OrderedSet[Statement]) => 
        //if(index.name=="defguard0") {
        //    println("[" + Console.BLUE + "Add defguard" + Console.RESET + s"]   ${index}    ->    $stmt            hashcode: ${stmt.hashCode}")
        //    println("[" + Console.BLUE + "Existing guards" + Console.RESET + s"]   index: ${index}")
        //    stmtSet.foreach(stmt => println(s"$stmt        hashcode: ${stmt.hashCode}"))
        //} 
        if(stmtSet.contains(stmt)) {  
         // Duplicated stmt
          if( isSlangSubcontext() ) {
            // No reason to print this: it nags me when I repeat myself which I do.  Chase 6/10/19.
            // println("[" + Console.RED + "Duplicated Slang construct" + Console.RESET + s"]  ${index}   ->   $stmt     stmt hashcode: ${stmt.hashCode}")
            //println("[" + Console.BLUE + "Existing statements" + Console.RESET + s"]   index: ${index}")
            //stmtSet.foreach(stmt => println(s"$stmt        hashcode: ${stmt.hashCode}"))
          } else {
            println("[" + Console.RED + "Duplicated stmt" + Console.RESET + s"]: $stmt")
          }
        } else {
          stmtSet += stmt
        }
      case _ => 
        val stmtSet = OrderedSet[Statement](stmt)
        stmtsMap(index) = stmtSet
    }
  }

  /**
   * Add queries into the Subcontext
   */
  def addQueries(qs: Iterable[Statement]): Unit = {
    queries ++= qs
  }
}

object Subcontext {
  def apply(id: String): Subcontext = Subcontext(new SetId(id), None, None, OrderedSet[String](), 
      MutableMap[Index, OrderedSet[Statement]](), MutableMap[Index, OrderedSet[Statement]](), 
      OrderedSet[Statement]()) 

  def apply(id: String, statements: Map[Index, OrderedSet[Statement]], queries: Iterable[Statement]): Subcontext = {
    val subcontext = Subcontext(id)
    subcontext.addStatements(statements)
    subcontext.addQueries(queries)
    subcontext
  }

  def apply(id: String, statements: Map[Index, OrderedSet[Statement]]): Subcontext = {
    val queryIdx: Index = new Index("_query")
    val queries = statements.get(queryIdx).getOrElse(OrderedSet.empty[Statement])
    Subcontext(id, statements - queryIdx, queries)
  }
}
