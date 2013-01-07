//-----------------------------------------------------------------------------------------------------
//------------------------------------------ TABLE OF CONTENTS ----------------------------------------
//-----------------------------------------------------------------------------------------------------
// 1. Globals - globally scoped functions, type aliases, and variables that are used across compilation
// 2. Parser - syntactic rules for the Kiama parser. Turns source strings into Abstract Syntax Tree
// 3. \Lambda F - System F representation of the input program, translated from the AST
// 4. \Lambda K - Continuation Passing Style to linearise the program, with continuation tail calls
// 5. \Lambda C - Closure Conversion that separates a function from its environment (free variables)
// 6. \Lambda H - Hoisting that lifts all now closed functions to the top level of the program
// 7. TAL - Idealised Assembly Language emission that can be computed by the VM to garner a result
// 8. \Lambda H Virtual Machine that can interpret and compute \Lambda H intermediate language code
// 9. TAL Virtual Machine that can interpret and compute Idealised Assembly Language
// 10. Register Manager that fetches values from the heap, in to pseudo-registers adhoc during runtime
//
// 	NOTE: Concepts/structures that are the same across phases will only be explained in comments the
//	first time they are encountered in the code. This is to prevent cluttering the code with comments
//-----------------------------------------------------------------------------------------------------
//-------------------------------------------- START: GLOBALS -----------------------------------------
//-----------------------------------------------------------------------------------------------------
/** Set this to the directory that phase output can be written to.
	NOTE: Omit trailing slash */
val home_dir = ""

/** Flag that controls whether breakpoints are used during execution.
	This allows one to leave breakpoints in their code for future 
	testing, but have them not interfere in the meantime */
val debug_mode : Boolean = false


/** Type aliases used throughout */
type Num = Integer /** Numbers */
type Idn = String /** Identifiers */

/** Global counter to append to fresh var idns*/
var counter = -1
/** This function guarantees to return a fresh idn because
	it appends the value of the counter to the given arg */
def Fresh(x: Idn) = {
  /** Increment counter to ensure value is always unique */
  counter += 1
  /** Fresh idn is original idn with counter value appended */
  x ++ "_" ++ counter.toString()
}

/** Base class for primitive binary operators 
	NOTE: These are globally defined as their usage is constant 
	across phases, and thus they need not be translated */
abstract class Prim

/** Plus binary operator */
case class Prim_Plus() extends Prim {

	override def toString = " + "
}

/** Minus binary operator */
case class Prim_Minus() extends Prim {

	override def toString = " - "
}

/** Mult binary operator */
case class Prim_Mult() extends Prim {

	override def toString = " * "
}

/** Writes the given content to the application's working dir */
def FileOut( filename : String, content : Any ){
	try { 
		/** Relies on Java's file stream to write the file */
		var out_file = new java.io.FileOutputStream(home_dir + "/" +filename) 
		var out_stream = new java.io.PrintStream(out_file) 
		out_stream.print(content)
		out_stream.flush
		out_stream.close 
   } catch {
     case e: Exception => println(e)
   }
	
}

/** Provides a generic string representation of a generic list */
def ListString(list : List[Any]) : String = {

	var s = ""
	/** Concantenate all elements' string representations */
	for(i <- 0 until list.length){
   
		s = s + list(i)
		
		/** Only add a comma if this is not the last element */
		if( (i + 1) < list.length ) s = s + ", "
	
	}
	return s
}
/** Provides a generic string representation of a Idn->HVal mapping*/
def MapString(map : Map[Idn,HVal]) : String = {

	var s = ""
	/** Concantenate all elements' string representations */
	map.keys.map{ k =>	
		s = s + "\n" + k + " -> " + map(k) 
	}
	return s
}


/** Simulates a code breakpoint that suspends execution during testing */
def DebugBreakpoint( s : String) : Unit ={
	/** Only show the breakpoint if we are in Debug mode */
	if(debug_mode){
		/** Show the given string to the user */
		println("\n" + s + "\n\nPress enter to continue")
		/** Suspend execution until the read is happy to continue */
		Console.readLine
	}
}

/** Convenience method to compile and execute source code, with optional output 
	of intermediate code */
def Exec(s : String, phase_output : Boolean) : Unit = Run( Compile(s, phase_output ) )

/** Overload that assumes no phase output */
def Exec(s : String) : Unit = Exec( s, false )

/** Run a previously compiled program */
def Run(prog : TALProg) : Unit = TAL_VirtualMachine( prog ) .run

/** Compiles the given source code string, with the option of outputting
	the intermediate phase representations to file for reviewing later */
def Compile(s : String, phase_output : Boolean ) : TALProg = {
	
	/** To test execution time take the current time at initial function invocation */
	var start = System.currentTimeMillis
	
	/** Parse the given source code string to \F */
	val parsed = Parse__F(s).asInstanceOf[FTerm]
	/** Translation of \F -> \K, Continuation Passing Style */
	val k = F__K(parsed, parsed.tau)
	/** Translation of \K -> \C, Closure Conversion */
	val c = K__C(k)
	/** Translation of \C -> \H, Hoisting */
	val h = C__H(c)
	/** Emission of TAL */
	val idl = HProg__TALProg(h)
	
	/** Print the total time taken for compilation */
	DebugBreakpoint("Compile Time: " + (System.currentTimeMillis - start))
	
	/** If phase output is enabled, write the intermediate representation of each
		phase to file */
	if ( phase_output ){
		FileOut("outputF.txt", parsed)
		FileOut("outputK.txt", k)
		FileOut("outputC.txt", c)
		FileOut("outputH.txt", h)
		FileOut("outputIDL.txt", idl)
	}
	
	/** Return the compiled program */
	idl	
}

//-----------------------------------------------------------------------------------------------------
//-------------------------------------------- END: GLOBALS -------------------------------------------
//-----------------------------------------------------------------------------------------------------

//-----------------------------------------------------------------------------------------------------
//----------------------------------------- START: PARSER -> \F ---------------------------------------
//-----------------------------------------------------------------------------------------------------
/** Kiama is used to carry out the lexing and parsing preprocessing stages of the compiler */
object Parser extends org.kiama.util.ParserUtilities {

  lazy val start_exp = phrase (exp)
  lazy val start_typ = phrase (typ)
 
 
  /** Here the parser rules are defined for each term.
	  NOTE: These must be in order for precendence */
  lazy val exp : PackratParser[FTerm] =
		/** Fix rule, FIX x (x1) IN e */
		("FIX" ~> variable) ~ ("(" ~> variable <~ ")" ) ~ ("IN" ~> exp ) ^^ { case x ~ x1 ~ e => FTerm_Fix(x, x1, FType_Int(), FType_Int(),e) } | 
		/** If0 rule, IF0(e1,e2,e3)*/
		("IF0(" ~> exp ) ~ ("," ~> exp) ~ ("," ~> exp <~ ")") ^^ { case e1 ~ e2 ~ e3 => FTerm_IfZero(e1,e2,e3) }|
		/** Switch rule (syntactic sugar), SWITCH(e1,...,en) */
		("SWITCH" ~> ("(" ~> exp <~ "," ) ~ rep1sep(exp, ",") <~ ")" )^^ { case x ~ xs => SyntacticSugar.Switch(x :: xs) } |
		/** Addition rule, e1 + e2 */
		exp ~ ("+" ~> exp) ^^ { case l ~ r => FTerm_PrimOp(l, Prim_Plus(), r) } |
		/** Multiplication rule, e1 * e2 */
		exp ~ ("*" ~> exp) ^^ { case l ~ r => FTerm_PrimOp(l, Prim_Mult(), r) } |
		/** Subtraction rule, e1 - e2 */
		exp ~ ("-" ~> exp) ^^ { case l ~ r => FTerm_PrimOp(l, Prim_Minus(), r) } |
		/** Type Application rule, e[t] */
		exp ~ ("[" ~> typ <~ "]") ^^ { case e ~ t =>  FTerm_TypeApp(e,t) } |
		/** Projection rule, #n(tup) */
		("#" ~> integer ) ~ ( "(" ~> exp <~ ")" ) ^^ { case i ~ e => FTerm_Proj( i.i, e ) } | // #i(exp)
		variable ~ (":" ~> typ) ^^ { case e ~ t => { 
			e.tau = t
			(e)
		} }|
		/** Application rule, (f)(n) */
		repN(2, "(" ~> exp <~ ")") ^^ { case bracs =>  FTerm_App( bracs(0), bracs(1) ) } | 
		/** Tuple rule, (e1,...,en) */
		("(" ~> exp <~ "," ) ~ rep1sep(exp, ",") <~ ")" ^^ { case x ~ xs => FTerm_Tuple(x :: xs) } |
		/** Rule to recognise expressions wrapped in parantheses */
		"(" ~> exp <~ ")" |
		/** Application rule (without parantheses), f n */
		exp ~ exp ^^ { case l ~ r =>  FTerm_App(l,r) } |
		/** Variable rule, defined below */
		variable |
		/** Integer rule, defined below */
		integer |
		/** No recognised expression error */
		failure ("expression expected")
		
  /** Here the parser rules are defined for each type.
	  NOTE: These must be in order for precendence */
  lazy val typ : PackratParser[FType] =
	/** Function rule, t1 -> t2 */
    typ ~ ("->" ~> typ) ^^ FType_Fun |
	/** Universal quantification rule, ALL a.t */
   ("ALL" ~> typevariable) ~ ("." ~> typ) ^^ FType_All |
    /** Type Variable rule, a */
	typevariable |
	/** Type Tuple rule, (t1,...,tn) */
    ("(" ~> typ <~ "," ) ~ rep1sep(typ, ",") <~ ")" ^^ { case t ~ ts => FType_Tuple(t :: ts) } |
	/** No recognised type error */
	failure ("type expected")
	
	/** Integers rule, 9 | -9 */
	lazy val integer = "[-]?[0-9]+".r ^^ (s => FTerm_Int (s.toInt))
	/** Variable rule, varname */
	lazy val variable = idn ^^ { case i => FTerm_Var(i) }
	/** Identifier rule, varname */
	lazy val idn = not (keyword) ~> "[a-zA-Z][a-zA-Z0-9]*".r
	/** Type Variable rule, 'a */
	lazy val typevariable = typidn ^^ FType_Var
	/** Type Variable Identifier rule, 'a */
	lazy val typidn = "\'[a-zA-Z][a-zA-Z0-9]*".r
	/** Keyword rule, INT */
	lazy val keyword = "int[^a-zA-Z]".r ^^ (s => FType_Int) 
}

/** Takes a string representing code written in the source language,
	and attempts to parse it to \F */
def Parse__F(s : String) : F = {
	try{
		/** Try to parse an FType first */
		Parser.parse(Parser.start_typ, s).get 
	}
	catch{
		/** If passing an FType fails, try to parse an FTerm */
		case e : Exception =>  {
			println("No FType found, parsing for FTerm...")
			Parser.parse(Parser.start_exp, s).get
		}
	}
}

/** This is a static class for parsing syntantic sugar that allows the programmer to write 
	common code constructs that get translated to their equivalent in-memory representation */
object SyntacticSugar{
	/** Creates the necessary objects to simulate a switch statement with multiple case labels */
	def Switch(es : List[FTerm]) : FTerm_Fix = {
		/** Recursive auxiliary function that nests If0's used to model the cases */
		def aux(funs : List[FTerm], case_n : Int) : String ={
			/** NOTE: Nil list is considered semantically and syntactically invalid */
			
			/** If the tail of the list contains just one element it is treated as the default case */
			if (funs.tail.length == 1) "IF0(n - " + case_n + ", " + funs.head.toString + ", " + funs.last.toString + ")"
			/** Otherwise, nest the next case inside the else branch of the preceding If0 */
			else "IF0(n - " + case_n + ", " + funs.head.toString + ", " + aux(funs.tail, case_n + 1 ) + ")"
		}
		/** This is the string representation of the whole term that simulates the switch */
		val term = "( FIX f ( n ) IN ( " + aux(es, 1) + " ))"
	
		/** Parse the string representation in to the required Fix construct*/
		Parse__F(term).asInstanceOf[FTerm_Fix]
	}
}
//-----------------------------------------------------------------------------------------------------
//------------------------------------------- START: \F -> \K -----------------------------------------
//-----------------------------------------------------------------------------------------------------

/** \F, The System F Calculus */
abstract class F{
	/** Returns the set of free variables */
	def FV() : Set[FTerm_Var] = Set[FTerm_Var]()
	/** Returns the set of free type variables */
	def FTV() : Set[FType_Var] = Set[FType_Var]()
	
	/** NOTE: By default the above functions return the empty set.
		This behaviour is overwritten where necessary by subclasses*/
}

/** Base class for \F types */
abstract class FType extends F
/** Base class for all \F terms */
abstract class FTerm extends F {
	/** This allows us to annotate an FTerm with an explicit type, 
		and pass the typing information around implicitly */
	var tau : FType = _
}

/** The type context Delta */
type FTypeContext = Set[FType]
/** The value context Gamma */
type FValueContext = Map[FTerm_Var,FType]

/** \F Type Variables in */
case class FType_Var(a : Idn) extends FType{
	override def toString = a
	
	override def FTV() : Set[FType_Var] = Set[FType_Var]( this )
}
/** \F Integer Types */
case class FType_Int() extends FType{

	override def toString = "INT"
}
/** \F Function Types */
case class FType_Fun(tau1 : FType, tau2 : FType) extends FType{
	
	override def toString = tau1 + "->" + tau2
	
	override def FTV() : Set[FType_Var] = tau1.FTV ++ tau2.FTV
}
/** \F Universal Quantification Types */
case class FType_All(a : FType_Var, tau : FType) extends FType{

	override def toString = "ALL " + a + ". " + tau
		
	override def FTV() : Set[FType_Var] = tau.FTV - a
}
/** \F Tuple Types */
case class FType_Tuple(taus : List[FType]) extends FType{
	
	override def toString = "<" + taus.toString + ">"
	
	override def FTV() : Set[FType_Var] = taus.map( t => t.FTV ).flatten.toSet
}

/** \F Variables */
case class FTerm_Var(x : Idn) extends FTerm{
	
	this.tau = FType_Var(x)
	
	override def toString = x
	
	override def FV() : Set[FTerm_Var] = Set[FTerm_Var]( this )
	
	override def FTV() : Set[FType_Var] = Set[FType_Var]( FType_Var(x) )
}
/** \F Integers */
case class FTerm_Int(i : Num) extends FTerm{
	
	this.tau = FType_Int()
	
	override def toString = i + ""
}
/** \F Fix, used to represent functions */
case class FTerm_Fix(x : FTerm_Var, x1 : FTerm_Var, tau1 : FType, tau2 : FType, e : FTerm) extends FTerm{
	
	this.tau = FType_Fun(tau1, tau2)
	
	override def toString = "FIX " + x + "(" + x1 + " : " + tau1 + ") : " + tau2 + "." + e
	
	override def FV() : Set[FTerm_Var] = (e.FV - x1) - x
	
	override def FTV() : Set[FType_Var] = (e.FTV -- tau1.FTV ) -- tau2.FTV
}
/** \F Applications, used to invoke functions */
case class FTerm_App(e1 : FTerm, e2 : FTerm) extends FTerm{

	this.tau = e2.tau
	
	override def toString = e1 + " " + e2
	
	override def FV() : Set[FTerm_Var] = e1.FV ++ e2.FV
	
	override def FTV() : Set[FType_Var] = e1.FTV ++ e2.FTV
	
}
/** \F Type Abstractions */
case class FTerm_CapLam(a : FType_Var, e : FTerm) extends FTerm{
	
	this.tau = FType_All(a, e.tau)
	
	override def toString = "CAPLAM " + a + ". " + e
	
	override def FV() : Set[FTerm_Var] = e.FV
	
	override def FTV() : Set[FType_Var] = e.FTV
}
/** \F Type Applications */
case class FTerm_TypeApp(e : FTerm, tau_ : FType) extends FTerm{

	override def toString = e + "[" + tau_ + "]"
	
	override def FV() : Set[FTerm_Var] = e.FV
	
	override def FTV() : Set[FType_Var] = e.FTV ++ tau.FTV
}
/** \F Tuples */
case class FTerm_Tuple(es : List[FTerm]) extends FTerm{

	this.tau = FType_Tuple(es.map(e => e.tau)) // explicitly setting type
	
	override def FTV() : Set[FType_Var] = es.map( e => e.FTV ).flatten.toSet
	
	override def FV() : Set[FTerm_Var] = es.map( e => e.FV ).flatten.toSet
}
/** \F Projections over Tuples */
case class FTerm_Proj(i : Num, e : FTerm) extends FTerm{

	this.tau = e.tau.asInstanceOf[FType_Tuple].taus(i)

	override def toString = "PI " + i + "(" + e + ")" 

	override def FTV() : Set[FType_Var] = e.FTV
	
	override def FV() : Set[FTerm_Var] = e.FV
	
}
/** \F Primitive Operations */
case class FTerm_PrimOp(e1 : FTerm, p : Prim, e2 : FTerm) extends FTerm{
	
	this.tau = FType_Int()

	override def toString = e1 + " " + p + " " + e2
	
	override def FTV() : Set[FType_Var] = e1.FTV ++ e2.FTV
	
	override def FV() : Set[FTerm_Var] = e1.FV ++ e2.FV
}
/** \F If0, a conditional expression with branches */
case class FTerm_IfZero(e1 : FTerm, e2 : FTerm, e3 : FTerm) extends FTerm{
	
	this.tau = e2.tau
	
	override def toString = "IF0(" + e1 + ", " + e2 + ", " + e3 + ")"
	
	override def FTV() : Set[FType_Var] = e1.FTV ++ e2.FTV ++ e3.FTV
	
	override def FV() : Set[FTerm_Var] = e1.FV ++ e2.FV ++ e3.FV
}
//-----------------------------------------------------------------------------------------------------
//------------------------------------------ END: PARSER -> \F ----------------------------------------
//-----------------------------------------------------------------------------------------------------

/** Encapsulates the complete translation \F -> \K */
def F__K( e : FTerm, tau : FType ) : KTerm = {

	e.tau = tau
	/** Returns a fully constructed CPS KTerm representing the program */
	FTerm__KTerm( Set[FType](),  Map[FTerm_Var,FType](), e, e.tau )( (y : KVal) => KTerm_Halt( FType__KType(tau), y ) )

}

/** Represents the \K type for a tau-continuation */
def N(tau : FType) : KType = KType_Cont(Nil, List[KType](FType__KType(tau)))

/** This function does substitution on types */
def FType__Subst(taup : FType, tau : FType, alpha : FType_Var) : FType = {
	/** Substitution is carried out differently for different types */
	taup match {
		/** No substitution on Type Variables */
		case FType_Var(a) => FType_Var(a)
		/** No substitution on Integer Types */
		case FType_Int() => FType_Int()

		case FType_Fun(tau1, tau2) => {
		
			var tau1_ = tau1
			var tau2_ = tau2
			
			if (tau1 == tau) tau1_ = alpha
			if (tau2 == tau) tau2_ = alpha
			
			FType_Fun(tau1_, tau2_)
			
		}

		case FType_All(a, xtau) => {

			var a_ = a
			var tau_ = tau
			
			if (a == taup) a_ = alpha
			if (xtau == taup) tau_ = alpha
			
			FType_All(a_, tau_)
		}

		case FType_Tuple(taus) =>{ 
			
			var taus_ = List[FType]()
			/** Recursively call substitution function on each element */
			taus.map(tau_ => if (tau_ == tau) taus_ = alpha :: taus_ else taus_ = tau_ :: taus_ )
			
			FType_Tuple(taus_)
		}

	}
}
/** Convenience method to explicitly tell the Scala interpreter that a KType_Var 
	has been translated, as opposed to it complaining that the type is just KType */
def FType_Var__KType_Var(a : FType_Var) : KType_Var = a match {

	case FType_Var(x) => KType_Var(x)
}

/** Convenience method to explicitly tell the Scala interpreter that a KTerm_Var 
	has been translated, as opposed to it complaining that the type is just KTerm */
def FTerm_Var__KVal_Var(v : FTerm_Var) : KVal_Var = v match {

	case FTerm_Var(x) => KVal_Var(x)
}

/** Translates \F types to \K types, denoted by K[.] */
def FType__KType(tau: FType) : KType = tau match {
  
	case FType_Var(a) => KType_Var(a)

	case FType_Int() => KType_Int()

	/** The Function type is translated to a continuation */
	case FType_Fun(tau1, tau2) => KType_Cont(Nil, List[KType](FType__KType(tau1), N(tau2) ) )
	
	/** The Universal Quantification type  translation also involves a continuation */
	case FType_All(a, tau) => {
	
		var a_ = FType_Var__KType_Var(a)
	
		KType_Cont( List[KType_Var]( a_ ), List[KType]( N(tau) ) )
	}
	case FType_Tuple(taus) =>{
		/** Recursively translate each type in the tuple */
		var k_taus = taus.map( t => FType__KType(t) )
		
		KType_Tuple(k_taus)
	}		
}

/** Non tail-recursive translation \F -> \K, denoted by cps*
	NOTE: Type and Value contexts are added to recursively, hence they are required
	as arguments to this function. The FType arg is no longer needed after the addition
	of the .tau property, but is kept in to avoid possibility of regressive faults */
def FTerm__KTerm(delta: FTypeContext, gamma : FValueContext, e : FTerm, xtau : FType) : (KVal => KTerm) => KTerm = {

	DebugBreakpoint("FTerm__KTerm-> e : " + e.getClass + ", xtau : " + xtau.getClass )
	/** Need to create copycat vars for delta and gamma so that they can be modified 
		during the translation below */
	var delta_ = delta  
	var gamma_ = gamma 

	/** Use Scala's native match function to determine the type of the polymorphic e.
		NOTE: Matching on the type of e too, a form of typechecking */
	(e, e.tau) match {
		/** Integer translation is a straightforward 1:1 */
		case (FTerm_Int(i), FType_Int()) =>  (k : KVal => KTerm) => k(KVal_Int(i)) 
		
		case (FTerm_Var(x), _) => {

			var new_x = KVal_Var(x)
			/** Translate the variable's typing information too */
			new_x.tau = FType__KType(e.tau)
			
			(k : KVal => KTerm) => k(new_x)
		}

		case (FTerm_Fix(x, x1, tau1, tau2, e), FType_Fun(tau1_, tau2_)) =>{

			e.tau = tau2
			/** This complex translation utilises a tail recursive translation, 
			and adds to the Value context */
			var e1  = FTerm__KTerm_TailRec(delta_, gamma_ ++ Map[FTerm_Var,FType]( x -> FType_Fun(tau1, tau2), x1 -> tau1  ), e, e.tau)
			
			var c = KVal_Var(Fresh("c"))
			c.tau = N(tau2)
			
			var x_ : KVal_Var = FTerm_Var__KVal_Var(x) 
			var x1_ : KVal_Var = FTerm_Var__KVal_Var(x1)
			
			x1_.tau = FType__KType(tau1)
			
			(k : KVal => KTerm) => k(KVal_Fix(x_, Nil, List[(KVal_Var,KType)]( (x1_, x1_.tau ), (c, c.tau )), e1( c )))
		}
		
		/** App translation is interesting as it requires knowledge of types for 
			both e1 and e2, hence the later advent of .tau */
		case (FTerm_App(e1, e2), _ ) =>{
			/** The type of e1 becomes the function type */
			e1.tau = FType_Fun(e2.tau, xtau)
			var e1p = FTerm__KTerm(delta_, gamma_, e1, e1.tau )
			var e2p = FTerm__KTerm(delta_, gamma_, e2, e2.tau )

			var z = KVal_Var(Fresh("z"))
			z.tau = FType__KType( xtau )
			
			(k : KVal => KTerm) => e1p( (y1 : KVal) => ( e2p( (y2 : KVal) => ( KTerm_App(y1, Nil, List[KVal](y2, KVal_Fix( KVal_Var(Fresh("_")), Nil, List[(KVal_Var, KType)]((z, z.tau )), k(z) )) ) ) ) ))																														
		}

		case (FTerm_CapLam(a, e), FType_All(a_, tau) ) => {
		
			e.tau = tau
			/** For the translation of e the Type context is added to */
			var e1 = FTerm__KTerm_TailRec(delta_ ++ Set[FType](a), gamma_, e, e.tau)
			
			var c =  KVal_Var(Fresh("c"))
			c.tau =  N(tau)
			
			(k : KVal => KTerm) => k(KVal_Fix( KVal_Var(Fresh("_")), List[KType_Var]( FType_Var__KType_Var(a) ), List[(KVal_Var,KType)](( c, c.tau )), e1( c )))
		}

		case (FTerm_TypeApp(e, tau), _) =>{ 

			e.tau match {
				/** Further typechecking to ensure the type of e is valid */
				case FType_All(a, tau1) => {
					
					e.tau = FType_All(a, tau1)
					var e1 = FTerm__KTerm(delta_, gamma_, e, e.tau )
			
					var z = KVal_Var(Fresh("z"))
					z.tau = FType__KType(FType__Subst(xtau, tau, a)) 
					
					(k : KVal => KTerm) => e1( (y : KVal) => KTerm_App(y, List[KType]( FType__KType(tau) ), List[KVal]( KVal_Fix( KVal_Var(Fresh("_")), Nil, List[(KVal_Var,KType)]((z, z.tau)), k( z ) ) ) ) )
				}
			
			}
			
		}

		case (FTerm_Tuple(es), FType_Tuple(taus) ) =>  (k: KVal => KTerm) => {
			
			/** Use of auxiliary function to perform complex nested of terms recursively */
			def aux(es : List[FTerm], vs : List[KVal], n : Num) : KTerm = es match {
			  /** Base case */
			  case Nil => k(KVal_Tuple(vs.reverse))
			  /** Whilst there are still elements left, we recursively nest them */
			  case (e::es) => {
					e.tau = taus(n)
					FTerm__KTerm(delta_, gamma_, e, e.tau)((y : KVal) => aux(es, y::vs, n+1)) 
				}
			}
			aux(es, Nil, 0)
		}

		case (FTerm_Proj(i, e), _ ) =>{ 
			e.tau match {
				/** Further typechecking to ensure the type of e is a Tuple that can be projected */
				case FType_Tuple(taus) => {											
					var z = KVal_Var(Fresh("z"))

					var e1 = FTerm__KTerm(delta_, gamma_, e, e.tau )
					
					(k : KVal => KTerm) => e1( (y : KVal) => KTerm_LetProj(z, i, y, k(z)))
				}
			}
		}
		case (FTerm_PrimOp(e1, p, e2), FType_Int()) =>{
			
			var z = KVal_Var(Fresh("z"))
			
			e1.tau = FType_Int()
			var e1p = FTerm__KTerm(delta_, gamma_, e1, e1.tau)
			e2.tau = FType_Int()
			var e2p = FTerm__KTerm(delta_, gamma_, e2, e2.tau)
			
			(k : KVal => KTerm) => e1p( (y1 : KVal) => ( e2p( (y2 : KVal) => (KTerm_LetPrimOp(z, y1 , p, y2, k(z) )) ) ) )
			
		}

		/** NOTE: If0 translation makes use of both tail-recursive and non tail-recursive
			translation functions */
		case (FTerm_IfZero(e1, e2, e3), _) => {

			e1.tau = FType_Int()
			var e1p = FTerm__KTerm(delta_, gamma_, e1, e1.tau)
			
			e2.tau = xtau
			var e2p = FTerm__KTerm_TailRec(delta_, gamma_, e2, e2.tau)
			
			e3.tau = xtau
			var e3p = FTerm__KTerm_TailRec(delta_, gamma_, e3, e3.tau)

			var c = KVal_Var(Fresh("c"))
			
			var z = KVal_Var(Fresh("z"))
			z.tau =  FType__KType(xtau)
			
			(k : KVal => KTerm) => e1p( (y : KVal) => (KTerm_Let(c, KVal_Fix( KVal_Var(Fresh("_")), Nil, List[(KVal_Var, KType)]( (z, z.tau ) ), k( z ) ), KTerm_IfZero(y, e2p(c), e3p(c)) )) )
		}


	}
}

/** Tail recursive translation \F -> \K, denoted by cps^t */
def FTerm__KTerm_TailRec(delta: FTypeContext, gamma : FValueContext, e : FTerm, xtau : FType) : (KVal => KTerm) = {
	
	DebugBreakpoint("FTerm__KTerm_TailRec-> e : " + e.getClass + ", xtau : " + xtau.getClass )
	
	/** The structure of this function is similar to the non tail-recursive companion
		function above. Comments will be brief for this function therefore */
	
	e.tau = xtau
	
	var delta_ = delta  
	var gamma_ = gamma 

	(e, e.tau) match { 
		
		case (FTerm_Int(i), FType_Int()) =>  (c : KVal) => KTerm_App(c, Nil, List[KVal]( KVal_Int(i) ) )
		
		case (FTerm_Var(x), FType_Var(a) ) => {
		
			var new_x = KVal_Var(x)
			new_x.tau = FType__KType(e.tau)
		
			(c : KVal) => KTerm_App(c, Nil, List[KVal]( new_x ) )
		
		}
		
		case (FTerm_Fix(x, x1, tau1, tau2, e), FType_Fun(tau1_, tau2_) ) => {

			e.tau = tau2
			var e1  = FTerm__KTerm_TailRec(delta_, gamma_ ++ Map[FTerm_Var,FType]( x -> FType_Fun(tau1, tau2), x1 -> tau1  ), e, e.tau)
			
			var c1 = KVal_Var(Fresh("c"))
			c1.tau = N(tau2)
			
			var x_ : KVal_Var = FTerm_Var__KVal_Var(x) 
			var x1_ : KVal_Var = FTerm_Var__KVal_Var(x1)
			
			x1_.tau = FType__KType(tau1)

			(c : KVal) => KTerm_App(c, Nil, List[KVal]( KVal_Fix(x_, Nil, List[(KVal_Var, KType)]( (x1_, FType__KType(tau1)), ( c1, c1.tau) ), e1( c1 ) ) ) )
																													
		}
		
		case (FTerm_App(e1, e2), _ ) =>{
				
			e1.tau = FType_Fun(e2.tau, xtau)
			var e1p = FTerm__KTerm(delta_, gamma_, e1, e1.tau )
			var e2p = FTerm__KTerm(delta_, gamma_, e2, e2.tau )

			(c : KVal) => e1p( (y1 : KVal) => e2p( (y2 : KVal) => KTerm_App(y1, Nil, List[KVal](y2, c) ) ) )
		}

		case (FTerm_CapLam(a, e), FType_All(a_, tau) ) => {
						
			e.tau = tau
			var e1 = FTerm__KTerm_TailRec(delta_ ++ Set[FType](a), gamma_, e, e.tau)
			
			var c =  KVal_Var(Fresh("c"))
			c.tau =  N(tau)
		
			(c) => KTerm_App(c, Nil, List[KVal]( KVal_Fix(  KVal_Var(Fresh("_")), List[KType_Var]( FType_Var__KType_Var(a) ), List[(KVal_Var,KType)]( (c.asInstanceOf[ KVal_Var], c.tau) ), e1(c) ) ) ) 
																																
		}

		case (FTerm_TypeApp(e, tau), _ ) =>{
			
			e.tau match {
				case FType_All(a, tau1) => {
						
						e.tau = FType_All(a, tau1)
						var e1 = FTerm__KTerm(delta_, gamma_, e, e.tau)
			
						(c : KVal) => e1( (y : KVal) => KTerm_App(y, List[KType]( FType__KType(tau) ), List[KVal](c) ) )
				
				}
			}
			
		
		}
		
		case (FTerm_Tuple(es), FType_Tuple(taus) ) => (c : KVal) => {

			def aux(es : List[FTerm], vs : List[KVal], n : Num) : KTerm = es match {
			  
			  case Nil => KTerm_App(c, Nil, vs.reverse)
			  case (e::es) => {
			  
					e.tau = taus(n)
					FTerm__KTerm(delta_, gamma_, e, e.tau )((y : KVal) => aux(es, y::vs, n+1))
				}
			
			}
			
			aux(es, Nil, 1) 
		}


		case (FTerm_Proj(i, e), _ ) =>{ 
			e.tau match {
				
				case FType_Tuple(taus) => {					
					var z = KVal_Var(Fresh("z"))
					
					var e1 = FTerm__KTerm(delta_, gamma_, e, e.tau )
					
					(c : KVal) => e1( (y : KVal) => KTerm_LetProj(z, i, y, KTerm_App(c, Nil, List[KVal](z) )  ) )
				}
			}
		}
		
		case (FTerm_PrimOp(e1, p, e2), FType_Int()) =>{
			
			e1.tau = FType_Int()
			var e1p = FTerm__KTerm(delta_, gamma_, e1, e1.tau )
			
			e2.tau = FType_Int()
			var e2p = FTerm__KTerm(delta_, gamma_, e2, e2.tau )
			
			var z = KVal_Var( Fresh("z") )
			
			(c : KVal) => e1p( (y1 : KVal) => e2p( (y2 : KVal) => KTerm_LetPrimOp(z , y1, p, y2, KTerm_App(c, Nil, List[KVal](z) )  ) ) )

		}

		case (FTerm_IfZero(e1, e2, e3), _) => {

			e1.tau = FType_Int()
			var e1p = FTerm__KTerm(delta_, gamma_, e1, e1.tau )
			
			e2.tau = xtau
			var e2p = FTerm__KTerm_TailRec(delta_, gamma_, e2, e2.tau)

			e3.tau = xtau
			var e3p = FTerm__KTerm_TailRec(delta_, gamma_, e3, e3.tau)

			(c : KVal) => e1p( (y : KVal) => KTerm_IfZero(y, e2p(c), e3p(c) ) )
														
		}

	}
}
		
//****************************************************************************************************

//-----------------------------------------------------------------------------------------------------
//------------------------------------------- START: \K -> \C -----------------------------------------
//-----------------------------------------------------------------------------------------------------

/** \K, The Continuation Passing Style Calculus */
abstract class K {

	def FV() : Set[KVal_Var] = Set[KVal_Var]()
	def FTV() : Set[KType_Var] = Set[KType_Var]()
}

abstract class KType extends K {
	/** This function provides an OO translation for types */
	def Type_K__C : CType
}

abstract class KTerm extends K {
	
	/** some terms do not need a type, but the functions in places require 
	a type param so we will set this to be KType_Int() just to satisfy those 
	places. This will be overriden where neccessary in the subclasses so 
	should not be an issue, as it will not be referenced in the actual function 
	anyway when it is not needed */
	var tau : KType = KType_Int() 
}

abstract class KVal extends K {

	var tau : KType = KType_Int()

}

/** \K Type context */
type KContext_Delta = Set[KType_Var]
/** \K Value context */
type KContext_Gamma = Map[KVal_Var,KType]

/** \K Type Variables */
case class KType_Var(a : Idn) extends KType{
	override def toString = a
	
	override def Type_K__C : CType_Var = CType_Var(a)
	
	override def FTV() : Set[KType_Var] = Set[KType_Var]( this )
}
/** \K Integer Types */
case class KType_Int() extends KType {

	override def toString = "int"

	override def Type_K__C : CType_Int = CType_Int()

}
/** \K Continuation Function Types */
case class KType_Cont(as : List[KType_Var], taus : List[KType]) extends KType{

	override def toString = "All[" + ListString(as) + "].(" + ListString(taus) + ")->void"
		
	override def Type_K__C : CType_Exis = {
	
		val beta_var = CType_Var( Fresh("beta") )

		val fun = CType_Cont(as.map(a => KType_Var__CType_Var(a) ), beta_var :: taus.map(t => t.Type_K__C ) )
		
		val tup = CType_Tuple(List[CType]( fun, beta_var ) )
		
		/** Use of existential quantification on types */
		CType_Exis( beta_var, tup )
	
	}
	
	override def FTV() : Set[KType_Var] = taus.map( t => t.FTV ).flatten.toSet -- as.map( a => a.FTV ).flatten.toSet 
	 
}
/** \K Type Tuples */
case class KType_Tuple(taus : List[KType]) extends KType{

	override def toString = "<" + ListString(taus) + ">"
	
	override def Type_K__C : CType_Tuple = CType_Tuple(taus.map(t => t.Type_K__C ))
	
	override def FTV() : Set[KType_Var] = taus.map( t => t.FTV ).flatten.toSet
	
}

/** \K Integers */
case class KTerm_Int(i : Num) extends KTerm{

	this.tau = KType_Int() // explicitly setting type

	override def toString = i + ""
}
/** \K Applications */
case class KTerm_App(v : KVal, taus : List[KType], vs : List[KVal]) extends KTerm {
	
	override def toString = v + "[" + ListString(taus) + "](" + ListString(vs) + ")"
	
	override def FV() : Set[KVal_Var] = v.FV ++ vs.map( vx => vx.FV ).flatten.toSet
	
	override def FTV() : Set[KType_Var] =  v.FTV ++ taus.map( t => t.FTV ).flatten.toSet ++ vs.map( vx => vx.FTV ).flatten.toSet
}
/** \K If0 */
case class KTerm_IfZero(v : KVal, e1 : KTerm, e2 : KTerm) extends KTerm{

	override def toString = "If0(" + v + ", " + e1 + ", " + e2 + ")"
	
	override def FV() : Set[KVal_Var] = v.FV ++ e1.FV ++ e2.FV
	
	override def FTV() : Set[KType_Var] =  v.FTV ++ e1.FTV ++ e2.FTV
	
}
/** \K Halt, used to signal the end of computation */
case class KTerm_Halt(tau_ : KType, v : KVal) extends KTerm{
	
	this.tau = tau_
	
	override def toString = "halt [" + tau + "] " + v
	
	override def FV() : Set[KVal_Var] = v.FV
	
	override def FTV() : Set[KType_Var] =  tau.FTV ++ v.FTV
	
}
/** \K Let */
case class KTerm_Let(x : KVal_Var, v : KVal, e : KTerm) extends KTerm{
	
	override def toString = "let " + x + " = " + v + " in " + e
	
	override def FV() : Set[KVal_Var] = (e.FV - x) ++ v.FV
	
	override def FTV() : Set[KType_Var] = (e.FTV -- x.FTV) ++ v.FTV
	
}
/** \K Let Projections */
case class KTerm_LetProj(x : KVal_Var, i : Num, v : KVal, e : KTerm) extends KTerm{
	
	override def toString = "let " + x + " = pi" + i + "(" + v + ") in " + e
	
	override def FV() : Set[KVal_Var] = (e.FV - x) ++ v.FV
	
	override def FTV() : Set[KType_Var] =   (e.FTV -- x.FTV) ++ v.FTV
}
/** \K Let Primitive Operations */
case class KTerm_LetPrimOp(x : KVal_Var, v1 : KVal, p : Prim, v2 : KVal, e : KTerm) extends KTerm{
	
	override def toString = "let " + x + " = " + v1 + " " + p + " " + v2 + " in " + e
	
	override def FV() : Set[KVal_Var] = (e.FV - x) ++ v1.FV ++ v2.FV
	
	override def FTV() : Set[KType_Var] =  (e.FTV -- x.FTV) ++ v1.FTV ++ v2.FTV
	
}

/** \K Value Variables */
case class KVal_Var(x : Idn) extends KVal{

	this.tau = KType_Var(x) // explicitly setting type
	
	override def toString = x
	
	override def FV() : Set[KVal_Var] = Set[KVal_Var]( this )
	
	override def FTV() : Set[KType_Var] =  Set[KType_Var]( KType_Var(x) )
}
/** \K Integers */
case class KVal_Int(i : Num) extends KVal{

	this.tau = KType_Int() // explicitly setting type

	override def toString = i + ""
}
/** \K Value Integers */
case class KVal_Tuple(vs : List[KVal]) extends KVal {

	this.tau = KType_Tuple(vs.map(v => v.tau)) // explicitly setting type
	
	override def toString = "<" + ListString(vs) + ">"
	
	override def FV() : Set[KVal_Var] = vs.map( v => v.FV ).flatten.toSet
	
	override def FTV() : Set[KType_Var] =  vs.map( v => v.FTV ).flatten.toSet
}
/** \K Fix */
case class KVal_Fix(x : KVal_Var, as : List[KType_Var], taus : List[(KVal_Var,KType)], e : KTerm) extends KVal {

	this.tau = KType_Cont(as, taus.map(kv => kv._2))

	override def toString = "fix " + x + "[" + ListString(as) + "](" + ListString(taus) + ")." + e
	
	override def FV() : Set[KVal_Var] = (e.FV -- taus.map( kv => kv._1 ).toSet) - x
	
	override def FTV() : Set[KType_Var] = (e.FTV -- taus.map( kv => kv._2.FTV ).flatten.toSet ) -- x.FTV
	
}

//-----------------------------------------------------------------------------------------------------
//-------------------------------------------- END: \F -> \K ------------------------------------------
//-----------------------------------------------------------------------------------------------------

/** Convenience method for running the \K -> \C transaltion */
def K__C( e : KTerm) : CTerm = KTerm__CTerm( Set[KType_Var](), Map[KVal_Var,KType](), e, e.tau)

/** The following code is structured in a similar fashion to \F->\K.
	The reader should refer to the above for clarity to avoid cluttering
	the code with superfluous commments */

def KType__Subst(taup : KType, alpha : KType, tau : KType) : KType = taup match {

	case KType_Var(a) => KType_Var(a)

	case KType_Int() => KType_Int()

	case KType_Cont(as, taus) => {
		
		var as_ = as.map(a => if(a == tau) alpha else a )
		var taus_ = taus.map(t => if(t == tau) alpha else t ) 
		
		KType_Cont( as_.map( a => a.FTV ).flatten , taus_)
	
	}

	case KType_Tuple(taus : List[KType]) => {
	
		var taus_ = taus.map(t => if(t == tau) alpha else t ) 
			
		KType_Tuple(taus_)
	}

}

def KType_Var__CType_Var(kvar : KType) : CType_Var = kvar match {

	case KType_Var(x) => CType_Var(x)
}

def KVal_Var__CVal_Var(delta : KContext_Delta, kvar : KVal) : CVal_Var = kvar match {

	case KVal_Var(x) => {
	
		val c = CVal_Var(x)
		
		return c
	}
}



def KTerm__CTerm(delta : KContext_Delta, gamma : KContext_Gamma, e: KTerm, xtau : KType) : CTerm = {

	DebugBreakpoint("KTerm__CTerm-> e : " + e.getClass + ", xtau : " + xtau.getClass )
	
	var delta_ = delta  
	var gamma_ = gamma 

	e.tau = xtau
	
	e match {
  
		case KTerm_Int(i) => CTerm_Int(i)

		/** This rule has been modified from Morrisett et al (1998) to remove
			typing. Refer to the Thesis for a discussion on this */
		case KTerm_App(v, sigmas, vs) =>	{

			val z = Fresh("z")
			val z_code = z + "code"
			val z_env = z + "env"
			
			CTerm_Let( CVal_Var(z), KVal__CVal(delta_,gamma_,v, v.tau),  
				
				CTerm_LetProj(CVal_Var(z_code), 0, CVal_Var(z), CTerm_LetProj(CVal_Var(z_env), 1, CVal_Var(z), CTerm_ValApp( CVal_Var(z_code),  CVal_Var(z_env) :: vs.map{ __v => KVal__CVal(delta_,gamma_,__v,__v.tau)} )  ))
			)

		}  

		case KTerm_IfZero(v, e1, e2) => {
			
			v.tau = KType_Int()
			val v1 = KVal__CVal(delta_, gamma_, v, v.tau)

			val e1_ = KTerm__CTerm(delta_, gamma_, e1, e1.tau)
			val e2_ = KTerm__CTerm(delta_, gamma_, e2, e2.tau)
			
			CTerm_IfZero( v1, e1_, e2_)
			
		}

		case KTerm_Halt(tau, v) => {

			v.tau = tau
			val v1 = KVal__CVal(delta_, gamma_, v, v.tau)
			
			/** NOTE: Typing has been removed for now */
			CTerm_Halt( /** tau.Type_K__C, */ v1)
			
		}

		case KTerm_Let(x, v, e) => {
			

			val x_ = KVal_Var__CVal_Var(delta_, x)
			/** NOTE: Typing has been removed for now */
			/** x_.tau = v.tau.Type_K__C */
			
			val v_ = KVal__CVal(delta_, gamma_, v, v.tau) 
			
			var e_ = KTerm__CTerm(delta_, gamma_ ++ Map[KVal_Var,KType]( x -> v.tau ) , e, e.tau)
			
			CTerm_Let(x_, v_, e_)
			
		}
			
		case KTerm_LetProj(x, i, v, e) => {
			
			val x_ = KVal_Var__CVal_Var(delta_, x)
			/** NOTE: Typing has been removed for now */
			/** x_.tau = v.tau.asInstanceOf[KType_Tuple].taus(i).Type_K__C */
		
			val v_ = KVal__CVal(delta_, gamma_, v, v.tau)

			val e_ = KTerm__CTerm(delta_, gamma_ ++ Map[KVal_Var,KType](  x -> v.tau.asInstanceOf[KType_Tuple].taus(i)  ), e, e.tau)
			
			CTerm_LetProj(x_, i, v_, e_)			
		}
		
		case KTerm_LetPrimOp(x, v1, p, v2, e) => {
			
			val x_ = KVal_Var__CVal_Var(delta_, x)
			/** NOTE: Typing has been removed for now */
			/** x_.tau =  CType_Int() */

			v1.tau = KType_Int()
			var v1_ = KVal__CVal(delta_, gamma_, v1, v1.tau)
						
			v2.tau = KType_Int()
			var v2_ = KVal__CVal(delta_, gamma_, v2, v2.tau)
			
			val e_ = KTerm__CTerm(delta_, gamma_ ++ Map[KVal_Var,KType]( x -> KType_Int() ),  e, e.tau)

			CTerm_LetPrimOp(x_, v1_, p, v2_, e_)			
		}
	}   
}

def KVal__CVal(delta : KContext_Delta, gamma : KContext_Gamma, v : KVal, xtau : KType) : CVal = {

	DebugBreakpoint("KVal__CVal-> v : " + v.getClass + ", xtau : " + xtau.getClass )
	
	var delta_ = delta  
	var gamma_ = gamma 

	v match {
		
		case KVal_Var(x) => {
			
			var new_x = CVal_Var(x)
			/** NOTE: Typing has been removed for now */
			/** new_x.tau = v.Type_K__C */
			
			return new_x
		}
		case KVal_Int(i) =>
		{
			CVal_Int(i)
		}
		case KVal_Tuple(vs) =>{
		
			CVal_Tuple( vs.map( v => KVal__CVal(delta_, gamma_, v, v.tau) ) )
		}
		/** This rule performs the closure conversion, and has been modified 
		from Morrisett et al (1998) to remove typing. This is discussed in the Thesis*/
		case KVal_Fix(x, as, taus, e) => {

			val x_c = KVal_Var__CVal_Var(delta_, x)
			val x_env = x_c.x + "env"
						
			val ys = gamma_.map{kv => kv._1}
						
			val ys_index = ys.zipWithIndex.foldRight( KTerm__CTerm(delta_ ++ as,gamma_ ++ Map[KVal_Var,KType]( x -> x.tau ) ++ taus.map( kv => kv._1 -> kv._2 ), e,e.tau)) {case ((x, n), e) => CTerm_LetProj(KVal_Var__CVal_Var(delta_, x) , n, CVal_Var(x_env), e) } 
			
			/** NOTE: Typing has been removed for now */
			val v_code = CVal_FixCode(x_c, /** as.map{a => a.Type_K__C},*/ CVal_Var(x_env) :: taus.map{kv => KVal_Var__CVal_Var(delta_, kv._1) }, ys_index)

			/** Creating the environment for the closure */
			val v_env = CVal_Tuple( ys.map( y => KVal_Var__CVal_Var(delta_, y) ).toList )
			
			CVal_Tuple(List(v_code, v_env))
		}
	}
}

//***********************************************************************************************************

//-----------------------------------------------------------------------------------------------------
//------------------------------------------- START: \C -> \H -----------------------------------------
//-----------------------------------------------------------------------------------------------------

/** \C, The Closure Conversion Calculus */
abstract class C

abstract class CType extends C
abstract class CTerm extends C {
	/** NOTE: Typing has been removed for now */
	/** var tau : CType = _ */
}
abstract class CVal extends C {
	/** NOTE: Typing has been removed for now */
	/** var tau : CType = _ */
}
/** \C Type Context */
type CContext_Delta = Set[CType_Var]
/** \C Value Context */
type CContext_Gamma = Map[CVal_Var,CType]

/** \C Type Variables */
case class CType_Var(a : Idn) extends CType {
	override def toString = a
}
/** \C Integer Types */
case class CType_Int() extends CType {

	override def toString = "INT"
}
/** \C Continuation Function Types */
case class CType_Cont(as : List[CType_Var], taus : List[CType]) extends CType {
	
	override def toString = "All[" + ListString(as) + "].(" + ListString(taus) + ")->void"
}
/** \C Tuple Types */
case class CType_Tuple(taus : List[CType]) extends CType {

	override def toString = "<" + ListString(taus) + ">"
}
/** \C Existential Quantification Types */
case class CType_Exis(a : CType_Var, tau : CType) extends CType{
	
	override def toString = "Exis " + a + "." + tau
}
/** \C Integers */
case class CTerm_Int(i : Num) extends CTerm {
	/** this.tau = CType_Int() */
	
	override def toString = i + ""
}
/** \C Value Applications */
case class CTerm_ValApp(v : CVal, vs : List[CVal]) extends CTerm {

	override def toString = v + "(" + ListString(vs) + ")"
}
/** \C If0 */
case class CTerm_IfZero(v : CVal, e1 : CTerm, e2 : CTerm) extends CTerm{

	override def toString = "\n\tif0(" + v + ", " + e1 + ", " + e2 + ")"
}

/** \C Halt, NOTE: Typing has been removed for now */
case class CTerm_Halt( /** tau_ : CType, */ v : CVal) extends CTerm {
	/** this.tau = tau_ */

	override def toString = "\n\thalt " + v /** "\n\thalt[" + tau_ + "] " + v */
}
/** \C Let */
case class CTerm_Let(x : CVal_Var, v : CVal, e : CTerm) extends CTerm {

	override def toString = "\n\tlet " + x + " = " + v + " in " + e
}
/** \C Let Projections */
case class CTerm_LetProj(x : CVal_Var, i : Num, v : CVal, e : CTerm) extends CTerm {

		override def toString = "\n\tlet " + x + " = pi" + i + "(" + v + ") in " + e 
}
/** \C Let Primitive Operations */
case class CTerm_LetPrimOp(x : CVal_Var, v1 : CVal, p : Prim, v2 : CVal, e : CTerm) extends CTerm {

	override def toString = "\n\tlet " + x + " = " + v1 + " " + p + " " + v2 + " in " + e
}

/** \C Let Unpack Of Existential Types, NOTE: Typing has been removed for now so this is not used */
case class CTerm_LetUnpack(a : CType, x : CVal_Var, v : CVal, e : CTerm) extends CTerm{
	
	override def toString = "\n\tlet [" + a + ", " + x + "] = unpack " + v + " in " + e
}

/** \C Value Variables */
case class CVal_Var(x : Idn) extends CVal {
	/** this.tau = CType_Var(x) */
	
	override def toString = x
}
/** \C Value Integers */
case class CVal_Int(i : Num) extends CVal {
	/** this.tau = CType_Int() */
	
	override def toString = i + ""
}
/** \C Tuples */
case class CVal_Tuple(vs : List[CVal]) extends CVal {
	/** this.tau = CType_Tuple( vs.map( v => v.tau) ) */

	override def toString = "<" + ListString(vs) + ">"
}
/** \C Type Application */
case class CVal_TypeApp(v : CVal, tau_ : CType) extends CVal {

	override def toString = v + "[" + tau_ + "]"
}
/** \C Pack, allows use to abstract over Existential Types. NOTE: Typing has been removed for now */
case class CVal_Pack(tau_ : CType, v : CVal, exis : CType_Exis) extends CVal {
	/** this.tau = exis */
	override def toString = "\n\tpack [" + tau_ + ", " + v + "] as " + exis  
	
}
/** \C Fixcode construct introduced for closures */
case class CVal_FixCode(x : CVal_Var, /* as : List[CType_Var],*/ xs : List[CVal_Var], e : CTerm) extends CVal {
	/** this.tau = CType_Cont(as, taus.map{t => t.tau}) */

	override def toString = "\n\tfixcode " + x + /* "[" + ListString(as) + "]" + */ "(" + ListString(xs) + ")." + e 
}

//-----------------------------------------------------------------------------------------------------
//-------------------------------------------- END: \K -> \C ------------------------------------------
//-----------------------------------------------------------------------------------------------------

/** Helper method to assert that the type returned from a type var translation 
	is not just the generic HType */
def CType_Var__HType_Var(a : CType_Var) : HType_Var = CType__HType(a).asInstanceOf[HType_Var]

def CVal_Var__HVal_Var( v: CVal_Var, ls: Map[Idn, HVal]) : (HVal_Var, HContext_Heap ) = CVal__HVal(v, ls).asInstanceOf[(HVal_Var, HContext_Heap )]

/** Convenience method for the \C -> \H translation */
def C__H( e : CTerm ) : HProg  = {
	/** Begins with an empty Heap context */
	val (e_, heap) = CTerm__HTerm(e,  Map[Idn, HVal]() )

	HProg ( heap, e_ )
}

def CType__HType(tau: CType) : HType = tau match {

	case CType_Var(a) => HType_Var(a)

	case CType_Int() => HType_Int()

	case CType_Cont(as, taus) => HType_Cont( as.map(a => CType_Var__HType_Var(a) ), taus.map( t => CType__HType(t) ) )

	case CType_Tuple(taus) => HType_Tuple( taus.map( t => CType__HType(t) ) )

	case CType_Exis(a, tau) => HType_Exis( CType_Var__HType_Var(a), CType__HType(tau))
	
   
}

/** NOTE: xtau is not used as an arg here, it can be referenced direct via the 
	tau propert of a CTerm */
def CTerm__HTerm(  e: CTerm,  ls: Map[Idn, HVal] ) :  (HTerm, HContext_Heap ) = {
	
	DebugBreakpoint("CTerm__HTerm-> e : " + e.getClass /** + ", tau : " + e.tau.getClass */)
	
	/** Translation here is 1:1 and so more straightforward than translations before */
	e match {

		case CTerm_ValApp(v, vs) => {
		
			val (v_, heap) = CVal__HVal(v, ls)
			
			val (vs_, heaps) = vs.map{ CVal__HVal( _, ls ) }.unzip
			
			( HTerm_ValApp(v_, vs_), heap ++ heaps.flatten )
			
		}

		case CTerm_IfZero(v, e1, e2) => {
			
			val (v_, heap1) = CVal__HVal(v, ls)
			val (e1_, heap2) = CTerm__HTerm(e1, ls)
			val (e2_, heap3) = CTerm__HTerm(e2, ls)
		
			val ifzero = HTerm_IfZero(v_, e1_, e2_)
			
			(ifzero, heap1 ++ heap2 ++ heap3)
		}

		case CTerm_Halt( /** tau, */ v) => {
		
			val (v_, heap) = CVal__HVal(v, ls) 
			
			( HTerm_Halt( /** CType__HType(tau), */ v_ ), heap )
		}

		case CTerm_Let(x, v, e) => {
			
			val x_ = HVal_Var(x.x)
			
			val (v_, heap1) = CVal__HVal(v, ls)
			val (e_, heap2) = CTerm__HTerm(e, ls)
		
			val let = HTerm_Let(x_, v_, e_)
			
			(let, heap1 ++ heap2)
			
		}

		case CTerm_LetProj(x, i, v, e) => {

			val x_ = HVal_Var(x.x) 

			val (v_, heap1) = CVal__HVal(v, ls)
		
			val (e_, heap2) = CTerm__HTerm(e, ls)
	
			val proj = HTerm_LetProj(x_, i, v_, e_)
		
			(proj, heap1 ++ heap2 )
		}

		case CTerm_LetPrimOp(x, v1, p, v2, e) => { 
			
			val x_ = HVal_Var(x.x) 
			
			val (v1_, heap1) = CVal__HVal(v1, ls)
			val (v2_, heap2) = CVal__HVal(v2, ls)
			val (e_, heap3) = CTerm__HTerm(e, ls)
		
			val primop = HTerm_LetPrimOp( x_, v1_, p, v2_, e_ )
			
			( primop, heap1 ++ heap2 ++ heap3 )
		}

		/** This translation is not utilised at present */
		case CTerm_LetUnpack(a, x, v, e) => { 

			val x_ = HVal_Var(x.x)
			
			val (v_, heap1) = CVal__HVal(v, ls)
			val (e_, heap2) = CTerm__HTerm(e, ls)
			
			val unpack =  HTerm_LetUnpack( CType__HType(a), x_, v_, e_)
			
			( unpack, heap1 ++ heap2 )
		}
		
	}
}

/** NOTE: xtau is not used as an arg here, it can be referenced direct via the 
	tau propert of a CTerm */ 
def CVal__HVal(  v: CVal, ls: Map[Idn, HVal] ) : (HVal, HContext_Heap ) = 
{
	DebugBreakpoint("CVal__HVal-> v : " + v.getClass /** + ", tau : " + v.tau.getClass */ )

	v match {

		case CVal_Var(x) => {
			/** Fresh vars are only returned if x does not already
				exist on the heap */
			
			ls.get(x) match {
				case Some(v) => {
				
					(v, Map[HVal_Label, HBlock]() )
				}
				case None => {
				
					val res = HVal_Var(x)
					/** res.tau = CType__HType(v.tau) */
					
					(res, Map[HVal_Label, HBlock]() )
				}
			}
		}

		case CVal_Int(i) => {
		
			( HVal_Int(i), Map[HVal_Label, HBlock]() )
		}
		case CVal_Tuple(vs) => {

			val (vs_, heaps) = vs.map{ CVal__HVal(_, ls) }.unzip

			( HVal_Tuple(vs_), heaps.flatten.toMap )
		}
		
		case CVal_TypeApp(v, tau_) => {

			val (v_, heap) = CVal__HVal(v, ls)
			
			( HVal_TypeApp( v_, CType__HType(tau_) ), heap )
		
		}

		case CVal_Pack(tau_, v, exis) => {
			
			val (v_, heap) = CVal__HVal(v, ls)
			
			val exis_ : HType_Exis =  CType__HType(exis).asInstanceOf[HType_Exis]
			
			( HVal_Pack( CType__HType( tau_ ), v_, exis_ ), heap )

		}
		
		
		/** Everytime there is a fixcode we need to construct a block for it, 
			and assign a label pointing to it on the heap */
		case CVal_FixCode(x, /* as,*/ xs, e) => {
			
			/** start by creating a label that will be used to point to the block */
			val l = HVal_Label( Fresh(x + "_block") )

			/** The head contains the environment */
			val tup = HVal_Tuple( List[HVal]( l, HVal_Var(xs.head.x) ) ) 

			/** recursively translate the e term (function body), with the addition 
				of the new label */
			val (e_, heap) = CTerm__HTerm( e, ls + ( x.x -> tup ))
			
			val block = HBlock(xs.map{ case CVal_Var(_x) => HVal_Var(_x) }, e_)
			
			/** add the new block to the heap pointed to by the label */
			( l, heap ++ Map[HVal_Label, HBlock]( l -> block ) )
			
		}
		
	}
}

//-----------------------------------------------------------------------------------------------------
//------------------------------------------- START: \H -> TAL ----------------------------------------
//-----------------------------------------------------------------------------------------------------

/** \H, The Hoisting Calculus */
abstract class H

abstract class HType extends H
abstract class HTerm extends H {

	/** var tau : HType = _ */
}

abstract class HVal extends H {
	
	/** var tau : HType = _ */
	
	/** This retrieves the HVal relative to the given environment/context */
	def eval( context: Map[Idn, HVal] ) : HVal = this
}
 
/** \H Code Blocks */
case class HBlock ( /** as : List[HType_Var], */ args : List[HVal_Var], e : HTerm ) extends H {

	/** val tau = HType_Cont(as, args.map( x => x.tau )) */

	override def toString = "CODE [" + /** ListString(as) +*/ "](" + ListString(args) + ")." + e
	
}

/** \H Prog */
case class HProg (blocks : HContext_Heap, e : HTerm) extends H {
	
	override def toString = "LETREC " + blocks + " IN " + e
}

/** \H Type Context */
type HContext_Delta = Set[HType_Var]
/** \H Value Context */
type HContext_Gamma = Map[HVal_Var, HType]
/** \H Heap Context, containing labels mapped to code blocks */
type HContext_Heap = Map[HVal_Label, HBlock]

/** \H Type Variables */
case class HType_Var(x : Idn) extends HType {


}
/** \H Integer Types */
case class HType_Int() extends HType {

	override def toString = "INT"
}
/** \H Continuation Functions Types */
case class HType_Cont(as : List[HType_Var], taus : List[HType]) extends HType {

	override def toString = "ALL [" + ListString(as) + "].(" +  ListString(taus) + ") -> void"
}
/** \H Tuple Types */
case class HType_Tuple(taus : List[HType]) extends HType{

	override def toString = "<" +  ListString(taus) + ">"
}
/** \H Existential Quantification on Types */
case class HType_Exis(a : HType_Var, tau : HType) extends HType{

	override def toString = "EXIS " + a + "." + tau
}

/** \H Integers */
case class HTerm_Int(i : Num) extends HTerm{

	override def toString = i + ""
	
}
/** \H Value Applications */
case class HTerm_ValApp(v : HVal, vs : List[HVal]) extends HTerm{

	override def toString = v + "(" + ListString(vs) + ")"
}
/** \H If0 */
case class HTerm_IfZero(v : HVal, e1 : HTerm, e2 : HTerm) extends HTerm{

	override def toString = "IF0(" + v + ", " +  e1 + ", " + e2 + ")"
}
/** \H Halt */
case class HTerm_Halt( /** tau_ : HType, */ v : HVal) extends HTerm{ 

	override def toString = "\n\tHALT " + /** "[" + tau_ + "] " + */ v
}
/** \H Let */
case class HTerm_Let(x : HVal_Var, v : HVal, e : HTerm) extends HTerm{

	override def toString = "\n\tLET " + x + " = " + v + " IN " + e
}
/** \H Let Projections */
case class HTerm_LetProj(x : HVal_Var, i : Num, v : HVal, e : HTerm) extends HTerm{

		override def toString = "\n\tLET " + x + " = PI " + i + "(" + v + ") IN " + e
}

/** \H Let Primitive Operations */
case class HTerm_LetPrimOp(x : HVal_Var, v1 : HVal, p : Prim, v2 : HVal, e : HTerm) extends HTerm{

		override def toString = "\n\tLET " + x + " = " + v1 + " " + p + " " + v2 + " IN " + e
}
/** \H Let Unpack of Existentially packed types */
case class HTerm_LetUnpack(a : HType, x : HVal_Var, v : HVal, e : HTerm) extends HTerm{

		override def toString = "\n\tLET [" + a + ", " + x + "] = UNPACK " + v + " IN " + e
}

/** \H Value Variables */
case class HVal_Var(l : Idn) extends HVal{

		override def toString = l 
		/** look up by identifier */
		override def eval( context: Map[Idn, HVal]) : HVal = context(l) 
}
/** \H Labels, used on the Heap to reference code blocks */
case class HVal_Label(l : Idn) extends HVal{

		override def toString = l + " |"
}
/** \H Integer Values */
case class HVal_Int(i : Num) extends HVal{

		override def toString = i + ""
}
/** \H Tuples */
case class HVal_Tuple(vs : List[HVal]) extends HVal{

		override def toString = "<" + ListString(vs) + ">" 
		
		override def eval( context: Map[Idn, HVal]) : HVal = HVal_Tuple( vs.map( v => v.eval( context ) ) )
}
/** \H Type Applications */
case class HVal_TypeApp(v : HVal, tau_ : HType) extends HVal{

		override def toString = v + "[" + tau_ + "]"
		
		override def eval( context: Map[Idn, HVal]) : HVal = HVal_TypeApp( v.eval( context ), tau_ )
}
/** \H Pack, abstraction over Existential types */
case class HVal_Pack(tau_ : HType, v : HVal, exis : HType_Exis) extends HVal {

		override def toString = "PACK [" + tau_ + ", " + v + "] AS " + exis
		
		override def eval( context: Map[Idn, HVal]) : HVal = HVal_Pack(tau_, v.eval( context ), exis)
}
//-----------------------------------------------------------------------------------------------------
//-------------------------------------------- END: \C -> \H ------------------------------------------
//-----------------------------------------------------------------------------------------------------

def HType__TALType(tau : HType) : TALType = tau match {


	case HType_Var(x) => TALType_Var(x)

	case HType_Int() => TALType_Int()

	/** case HType_Cont(as, taus) =>  TALType_AllGam( as.map( a => HType__TALType(a).asInstanceOf[TALType_Var] ) , Map[Idn, TALType]( taus.map( t => Fresh("x") -> t ) ) ) */

	case HType_Tuple(taus) => TALType_Tuple( taus.map( HType__TALType ) )

	/** case HType_Exis(a, tau) => TALType_Exis( HType__TALType(a), HType__TALType(tau) ) */
}

def HTerm__TAL( e : HTerm ) : (Map[Idn, TALBlock], List[TALInst]) = {
	
	DebugBreakpoint("HTerm__TAL-> e : " + e.getClass /** + ", tau : " + e.tau.getClass */)

	e match {

		case HTerm_ValApp(v, vs) => {
			val reg0_ = Fresh("r0")
			val regs_ = vs.map((v) => Fresh("r") )
			
			/** Generate move instructions to put all values in register and jump to them */
			val mov0 = List( TALInst_Mov( reg0_, HVal__TALVal(v)) )
			
			val mov1 = for ((r, v) <- ( regs_ zip vs )) yield TALInst_Mov( r, HVal__TALVal(v) )
			val mov2 = for ((r, i) <- regs_.zipWithIndex) yield TALInst_Mov(Arg_Register(i), TALVal_Reg(r))
			val mov3 = List( TALInst_Jmp( TALVal_Reg( reg0_ ) ) ) 
			
			(Map(), mov0 ::: mov1 ::: mov2 ::: mov3)
			
		}
		

		case HTerm_IfZero(v, e1, e2) => {
			val l = Fresh("ELSE")
			val r = Fresh("r")
			
			/** get the TAL code for both of the branches in the IF */
			val ( exec1 , inst1 ) = HTerm__TAL(e1)
			val ( exec2, inst2 ) = HTerm__TAL(e2)
			
			/** use of the BNZ to decide which branch of the IF to execute */
			val emission = List( TALInst_Mov( r, HVal__TALVal(v)), TALInst_Bnz(r, TALVal_Label(l) ))
			
			val exec3 = TALBlock( Nil, inst2)
			
			( exec1 ++ exec2 + ( l -> exec3), emission ::: inst1 )
		}
		
		case HTerm_Halt( /** tau_, */ v) =>  ( Map(), List( TALInst_Mov(Arg_Register(0), HVal__TALVal(v)), TALInst_Halt()))
		
		case HTerm_Let(x, v, e) => {
			
			val (exec, inst) = HTerm__TAL(e)
			val emission = TALInst_Mov(Value_Register(x.l), HVal__TALVal(v))
			
			(exec, emission :: inst)
		
		}
		case HTerm_LetProj(x, i, v, e) => {
			
			val r = Value_Register(x.l)
			val (exec, inst) =  HTerm__TAL(e)
			
			val emission = List(TALInst_Mov( r, HVal__TALVal(v)), TALInst_Proj(r, r, i) )
			
			
			(exec, emission ::: inst)
		
		}
		
		
		case HTerm_LetPrimOp(x, v1, p, v2, e) => {
			
			val r = Value_Register(x.l)
			val (exec, inst) = HTerm__TAL(e)

			val emission = p match {
			
				case Prim_Plus() => List(TALInst_Mov( r, HVal__TALVal(v1) ), TALInst_Add( r, r, HVal__TALVal(v2) ) )
				case Prim_Minus() => List(TALInst_Mov( r, HVal__TALVal(v1) ), TALInst_Sub( r, r, HVal__TALVal(v2) ) )
				case Prim_Mult() => List(TALInst_Mov( r, HVal__TALVal(v1) ), TALInst_Mult( r, r, HVal__TALVal(v2) ) )
			}
			
			(exec, emission ::: inst)
		}
		
		/** case HTerm_LetUnpack(a, x, v, e) => */
	}

}


/** Translation of code blocks from \H -> TAL */
def HBlock__TALBlock(l : Idn, hblock : HBlock ) : List[(Idn, TALBlock)]  = hblock match {
 
	case HBlock( /** as,*/  args, e) => {
	
		val (exec, inst) = HTerm__TAL(e)
		
		(l, TALBlock( args.map( a => TALVal_Reg("REG_" + a.l) ), inst) ) :: exec.toList 
	
	}
}

/** Translation of programs from \H -> TAL */
def HProg__TALProg(prog : HProg) = prog match {

	case HProg(blocks, e) => {
		
		val (exec, inst) = HTerm__TAL(e)
		val blocks_ = for ((l, hblock ) <- blocks) yield HBlock__TALBlock(l.l, hblock )
		
		TALProg(exec ++ blocks_.flatten.toMap, inst)
	}
}

def HVal__TALVal( v : HVal) : TALVal = {
	DebugBreakpoint("HVal__TAL-> v : " + v.getClass /**+ ", tau : " + v.tau.getClass */)
	
	v match {

		case HVal_Var(x) => TALVal_Reg(Value_Register(x))	/** Register allocation */
		case HVal_Int(i) => TALVal_Int(i)
		case HVal_Tuple(vs) => TALVal_Tuple(vs.map( HVal__TALVal ))
		case HVal_Label(l) => TALVal_Label(l)

		case HVal_TypeApp(v_, tau_) => TALVal_TypeApp( HVal__TALVal(v_), HType__TALType(tau_) )
		
		case HVal_Pack(tau_, v, exis) => TALVal_Pack( HType__TALType(tau_), HVal__TALVal(v), HType__TALType(exis) )

	}
}
/** Helper functions to create conventional Register names */
def Value_Register(s: String) = "REG_" + s
def Arg_Register(i: Int) = "RARG_" + i.toString
	
/** TAL, Idealised Assembly Language*/
abstract class TAL

abstract class TALType extends TAL
abstract class TALTerm extends TAL {

	/** var tau : TALType = _ */
}

abstract class TALVal extends TAL {
	
	/** var tau : TALType = _ */
	
	def eval() : TALVal
}
 
/** TAL Type Variables */
case class TALType_Var(a : Idn) extends TALType
/** TAL Integer Types */
case class TALType_Int() extends TALType
/** TAL Universal Quantification on Gamma */
case class TALType_AllGam( as : List[TALType_Var], gamma : TAL_Gamma ) extends TALType
/** TAL Tuple Types */
case class TALType_Tuple( taus : List[TALType] ) extends TALType
/** TAL Existential Types */
case class TALType_Exis( a : TALType_Var, tau : TALType ) extends TALType
 /** TAL Registers, represents the idea of a register on the CPU that can hold a value */
case class TALVal_Reg(r: Idn) extends TALVal{

   override def toString = r + ">>" 
  override def eval() : TALVal = RegManager.get(r).eval()
}

/** TAL Instructions that are processed */
abstract class TALInst extends TAL{

	def run() : Map[Idn, TALVal] = RegManager.stack_mem
}

/** TAL Type Context */
type TAL_Delta = Set[TALType_Var]
/** TAL Value Context */
type TAL_Gamma = Map[Idn, TALType]
/** TAL Heap Context */
type TAL_Heap = Map[Idn, TALType]

/** TAL Label, used to reference code blocks on the heap */
case class TALVal_Label(l : Idn) extends TALVal{

	 override def toString = l 
	override def eval() : TALVal = TALVal_Label(l)
	
}
/** TAL Integers */
case class TALVal_Int(i : Num) extends TALVal {
	
	override def toString = i + ""
	
	override def eval() : TALVal = TALVal_Int(i)
}
/** TAL Tuples */
case class TALVal_Tuple( vs : List[TALVal]) extends TALVal {

	override def toString = "<" + ListString(vs) + ">"
	override def eval() : TALVal = TALVal_Tuple(vs.map( _.eval(  ) ) )
}
/** TAL Type Applications */
case class TALVal_TypeApp( v : TALVal, tau_ : TALType ) extends TALVal{

	 override def eval() : TALVal = TALVal_TypeApp(v.eval( ), tau_)
}

/** TAL Pack of Existential types */
case class TALVal_Pack( tau_ : TALType, v : TALVal, tau1 : TALType) extends TALVal {

	 override def eval( ) : TALVal = TALVal_Pack(tau_, v.eval( ), tau1)
}

/** NOTE: For arithmetic operations it is no longer sufficient to use just
	a primitive operations class - we convert each to its specific operation */
/** TAL Addition, an operation to compute the sum of two values */
case class TALInst_Add(r1 : Idn, r2 : Idn, v : TALVal) extends TALInst{

	override def run() : Map[Idn, TALVal] = (RegManager.get(r2), v) match {
	
		case (TALVal_Int(n), TALVal_Int(m)) => RegManager.stack_mem + (r1 -> TALVal_Int(n + m) )
		
		case (TALVal_Int(n), TALVal_Reg(r3)) => RegManager.get(r3) match {
		
			case TALVal_Int(m) => RegManager.stack_mem + (r1 -> TALVal_Int(n + m) )
			
			/** Type checking that the operands are integers */
			case _ => throw new IllegalArgumentException("ERR : NaN")
		}
		/** Type checking that the operands are integers */
		case _ => throw new IllegalArgumentException("ERR : NaN")
	}

}
/** TAL Subtraction, an operation to compute the subtraction of one value from another */
case class TALInst_Sub(r1 : Idn, r2 : Idn, v : TALVal) extends TALInst{

	override def run() : Map[Idn, TALVal] = (RegManager.get(r2), v) match {
	
		case (TALVal_Int(n), TALVal_Int(m)) => RegManager.stack_mem + (r1 -> TALVal_Int(n - m) )
		
		case (TALVal_Int(n), TALVal_Reg(r3)) => RegManager.get(r3) match {
		
			case TALVal_Int(m) => RegManager.stack_mem + (r1 -> TALVal_Int(n - m) )
			
			case _ => throw new IllegalArgumentException("ERR : NaN")
		}
		case _ => throw new IllegalArgumentException("ERR : NaN")
	}

}
/** TAL Multiplication, an operation to compute the product of two values */
case class TALInst_Mult(r1 : Idn, r2 : Idn, v : TALVal) extends TALInst{

	override def run() : Map[Idn, TALVal] = ( RegManager.get(r2), v) match {
	
		case (TALVal_Int(n), TALVal_Int(m)) => RegManager.stack_mem + (r1 -> TALVal_Int(n * m) )
		
		case (TALVal_Int(n), TALVal_Reg(r3)) => RegManager.get(r3) match {
		
			case TALVal_Int(m) => RegManager.stack_mem + (r1 -> TALVal_Int(n * m) )
			
			case _ => throw new IllegalArgumentException("ERR : NaN")
		}
		case _ => throw new IllegalArgumentException("ERR : NaN")
	}

}

/** TAL Projection */
case class TALInst_Proj(r1: Idn, r2 : Idn, i: Num) extends TALInst {
  override def toString = "LDI " + r1 + " <- " + r2 + "[" + i + "]" 
  
  override def run( ) : Map[Idn, TALVal] = { 
    
	RegManager.get(r2) match {
      case TALVal_Tuple(vs) => RegManager.stack_mem + (r1 -> vs(i)) 
      case _ => throw new IllegalArgumentException("ERR : Tuple required")
    }
  }
}
/** TAL Jump, used to jump to labelled code blocks */
case class TALInst_Jmp(v: TALVal) extends TALInst {
  override def toString = "JMP " + v
}
/** TAL Halt, the end of computation */
case class TALInst_Halt() extends TALInst { 
  override def toString = "HALT" 
}
/** TAL Break Not Zero, the equivalent of If0 */
case class TALInst_Bnz(r: Idn, v: TALVal) extends TALInst {
  override def toString = "BNZ " + r + " " + v
}
/** TAL Move, moves a given value in to a given register */
case class TALInst_Mov(r: Idn, v: TALVal) extends TALInst {
  override def toString = "MOV " + r + " " + v
  
  override def run( ) : Map[Idn, TALVal] = v match {
    case TALVal_Reg(r1) => RegManager.stack_mem + (r -> RegManager.get(r1)) 
    case _ => RegManager.stack_mem + (r -> v)
  }
}
/** TAL Code Block */
case class TALBlock( regs: List[TALVal_Reg], cs: List[TALInst]) {

	override def toString = "code (" + ListString(regs) + ").\n" + cs.map{_.toString + "\n"} + "\n"
}
/** TAL Program */
case class TALProg( blocks : Map[Idn, TALBlock], start: List[TALInst]){}

//-----------------------------------------------------------------------------------------------------
//-------------------------------------------- END: \H -> TAL -----------------------------------------
//-----------------------------------------------------------------------------------------------------

//-----------------------------------------------------------------------------------------------------
//------------------------------------------- VIRTUAL MACHINES ----------------------------------------
//-----------------------------------------------------------------------------------------------------
/** Base class for both Virtual Machines */
abstract class VirtualMachine{
	/** Function invoke execution of the compiled code */
	def run() : Unit
}

case class H_VirtualMachine(program : HProg) extends VirtualMachine {

	/** Convenience method to run the program */
	def run(){
		exec_term(program.e, Map[Idn, HVal]())
	}

	/** Intepret the given term */
	def exec_term(e : HTerm, context : Map[Idn, HVal]){
	
		e match {
		
			//case HTerm_Int(i) =>
		
			case HTerm_ValApp(v, vs) => {
				
				val res = ( v.eval( context ), vs.map( _.eval( context ) ) ) 

				res match {
					
					case ( HVal_Label(l), vs ) => exec_block( HVal_Label(l), vs, context )
					
					/** Basic typechecking */
					case _ => throw new IllegalArgumentException( "ERR : Label required. Found _1: " + res._1.getClass + "\n" + res._1  )
				}

			}
			
			case HTerm_IfZero(v, e1, e2) => {
				
				v.eval( context ) match {
					
					case HVal_Int(i) => {
						
						if (i == 0){ /** if v == 0 we execute the first branch, e1 */
							println("v was equal to 0 : " + i)
							exec_term( e1, context )
						}
						else { /** else we execute the second branch */
							println("v was NOT equal to 0 : " + i )
							exec_term( e2, context ) 
						}
						
						
					}
					/** Basic typechecking */
					case _ => throw new IllegalArgumentException( "ERR : Param 1 of If0 must be HVal_Int.")
				}
			}

			case HTerm_Halt( /** tau_, */ v) => println ("RESULT: " + v.eval( context ))

			case HTerm_Let(x, v, e) => {

				exec_term(e, context + ( x.l -> v.eval( context )  ) )
			}
	
		
			
			case HTerm_LetProj(x, i, v, e) => {

				v.eval( context ) match {
					
					/** Execute the ith member of the given tuple */
					case HVal_Tuple(vs) => exec_term(e, context + ( x.l -> vs(i) ) )
					/** Basic typechecking */
					case _ => throw new IllegalArgumentException( "ERR : Tuple required.")
				}
			}
			
		
			case  HTerm_LetPrimOp(x, v1, p, v2, e) => {

				(v1.eval( context ), p, v2.eval( context ) ) match {
					
					/** deduce the operator and calculate the result */
					case ( HVal_Int(m), Prim_Plus(), HVal_Int(n) ) =>  exec_term(e,  context + ( x.l -> HVal_Int(m + n) ) )
					
					case ( HVal_Int(m), Prim_Minus(), HVal_Int(n) ) => exec_term(e,  context + ( x.l -> HVal_Int(m - n) ) )
					
					case ( HVal_Int(m), Prim_Mult(), HVal_Int(n) ) => exec_term(e,  context + ( x.l -> HVal_Int(m * n) ) )
					/** Basic typechecking */
					case _ => throw new IllegalArgumentException("ERR : NaN")
					
				}
			}
			case HTerm_LetUnpack(a, x, v, e) => {
		
				exec_term( e, context + ( x.l -> v.eval( context )  ) )
			}
		}
	}
	
	/** Executes the code block referenced on the heap by the given label */
	def exec_block( l: HVal_Label, as: List[HVal], context : Map[Idn, HVal] ){
	
		val code = program.blocks(l)
		
		val context_ = ( code.args.map(_.l) zip as ).toMap  //HVal Hval
		
		exec_term( code.e , context ++ context_ )
		
	}

}

/** VM for interpreting the compiled TAL code */
case class TAL_VirtualMachine(program : TALProg) extends VirtualMachine {

	override def run() = {
	
		var start = System.currentTimeMillis
		
		exec_inst( program.start )
		
		DebugBreakpoint("TAL VM exec time: " + (System.currentTimeMillis - start))

	}
	
	def exec_inst( cs: List[TALInst] ){
		/** Show contents of Registers */
		println(RegManager.toString)

		cs match {
			  case ( TALInst_Halt() :: _ ) =>{
			  
				/** flush the registers at the end of execution */
				RegManager.flush()
				
				/** Show the result on the console */
				println ("RESULT : " + RegManager.get("RARG_0") )
				
			  }
			  case ( TALInst_Jmp( TALVal_Label(l) ) :: _ ) => exec_block( l )
			  
			  case ( TALInst_Jmp( TALVal_Reg(r) ) :: _ ) => RegManager.get(r) match {
				
					case TALVal_Label(l) => exec_block( l )
					case _ => throw new IllegalArgumentException("ERR : JMP made to invalid label. Using : " + r + ", found: " + RegManager.get(r).getClass + "\n\n" + RegManager.toString + "\n\n" + RegManager.stack_mem)
			  }
			  case ( TALInst_Bnz( r, TALVal_Label(l) ) :: cs ) => {
			  
				  RegManager.get(r) match {
						
						case TALVal_Int(i) =>{
							
							if (i == 0){
							
								 exec_inst( cs )
							}
							else {
								
								exec_block( l )
							}
						
						}
						case _ =>  throw new IllegalArgumentException( "ERR : Param 1 of If0 must be TALVal_Int.")
				  }
				  
			  }
			  case (c :: cs) => {
				
				RegManager.++( c.run( ) )
				
				exec_inst( cs )
			}
			  case Nil => throw new IllegalArgumentException("ERR : Empty set of Instructions")
		}
	
	}
	
	
	def exec_block( l: Idn) {
	
		val block = program.blocks(l)

		val regs_ = for ( ( r, n ) <- block.regs.zipWithIndex ) yield ( r.r, TALVal_Reg("RARG_" + n).eval(  ) ) 

		RegManager.++( RegManager.stack_mem ++ regs_.toMap )
		
		exec_inst( block.cs )
	}

}


//-----------------------------------------------------------------------------------------------------
//------------------------------------------- REGISTER MANAGER ----------------------------------------
//-----------------------------------------------------------------------------------------------------
object RegManager{
/** Manages the contents of CPU registers, fetching in values from RAM when required, and evicted those not needed */
		
		import java.util.Random
		val rdm = new Random()		
		
		/** Number of registers to simulate on the CPU */
		val REG_COUNT = 10
		/** Empty value that is in a register initially by default */
		val NULL_VAL = "____"
		
		var CPU_regs = new Array[TALVal](REG_COUNT)
		
		/** This represents the RAM, containing all variables */
		var stack_mem =  Map[Idn, TALVal]() 
		
		/** Maps Reg number to the Idn it holds a value for - this is for compatibility with existing code */
		var live_vars = Map[Int,Idn]()
		var last_use = scala.collection.mutable.Queue[Int]()
		
		/** Instantiate all Regs with a blank idn */
		for (i <- 0 until REG_COUNT ){ 
			live_vars += ( i -> NULL_VAL ) 
			
			last_use += (i)
		}
		
		
		/** Add method to create a new value in RAM */
		def +( kv :  (Idn, TALVal) ) : Unit = {
		
			
			/** Add to RAM */
			stack_mem = stack_mem + kv
			
			/** If Idn is in a register, update value as is now stale */
			var index = reg_contains( kv._1 )
			if ( index != -1 ) {			
				fetch( index, kv._1 )
			}
		}
		
		/** Add method to create all the values in RAM for the given map */
		def ++( m : Map[Idn, TALVal]) : Unit = m.map{ kv => RegManager.+(kv) }
		
		
		/** Clear a register in the CPU */
		def evict( reg_n : Int ) : Unit = {
		
			/** Check the reg is a valid index */
			if ( reg_n >= REG_COUNT ) throw new ArrayIndexOutOfBoundsException( reg_n + " is not in CPU Reg range of " + REG_COUNT )

			/** Look up the old idn for the register that will be cleared */
			val old_idn = live_vars( reg_n )
			
			/** If this was an empty entry before, just return as nothing to evict */
			if ( old_idn == NULL_VAL ) return
			
			
			/** Also retrieve the old val so we can check if its dirty */
			val old_val = CPU_regs( reg_n )
			
			/** Write the evicted value back to the stack memory if dirty */
			if ( stack_mem( old_idn ) != old_val ) stack_mem = stack_mem + ( old_idn -> old_val )
			
			/** Clear the register */
			live_vars = live_vars + ( reg_n -> NULL_VAL ) 			
		}
		
		/** Fetches a value from RAM and loads it in to the given register index */
		def fetch( reg_n : Int, x : Idn) : Unit =  {
			
			/** Check the reg is a valid index */
			if( reg_n >= REG_COUNT ) throw new ArrayIndexOutOfBoundsException( reg_n + " is not in CPU Reg range of " + REG_COUNT )
		
			/** Now we can safely write to the val to the available register */
			live_vars = live_vars + ( reg_n -> x ) /** replace existing idn */
			
			CPU_regs( reg_n ) = stack_mem(x) /** fetch in val from stack */
		
		}
		
		/** Check whether the CPU registers contain the value mapped to this Idn */
		def reg_contains( x : Idn ) : Int = {
			
			for (i <- 0 until live_vars.keys.size ){ 
				
				if ( live_vars(i) == x ) return i
			}
		
			return -1
		}
		
		/** Push the most recently read register to the back of the queue */
		def update_last_use(reg_n : Int) : Unit ={

			last_use.dequeueFirst(a => a == reg_n)
			last_use.enqueue(reg_n)
		}
		
		/** Retrieves a value from a CPU register, that is mapped to an Idn */
		def get( x : Idn ) : TALVal = {
			/** This is how we tested running the code without a RegisterManager */
			/** return stack_mem(x) */
	
			DebugBreakpoint("Attempting to retrieve " + x + " from registers")
			
			/** Check whether the Idn is in a register */
			var index = reg_contains( x )
			if ( index != -1 ){
				update_last_use(index)
			
				return CPU_regs( index ) // return the value		
			}
			/** If we get here, the value is not in the regs, so fetch it... */
			DebugBreakpoint("Not found val in registers so finding free reg...")
			
			val selected_reg = find_free_reg()
			
			DebugBreakpoint("selected_reg allocated is " + selected_reg )
			
			/** Fetch in new val */
			fetch( selected_reg, x )
			
			DebugBreakpoint("Valued fetched in for " + x + ", CPU_reg now contains " + CPU_regs( selected_reg ) )
			
			update_last_use(selected_reg)
			
			/** Return the now loaded value */
			return CPU_regs( selected_reg )
			

		}
		
		/** This returns the index of a register that can be used */
		def find_free_reg() : Int = {
			
			/** First we search for an empty register we can use */
			for (i <- 0 until live_vars.keys.size ){ 
				
				/** If found an empty reg, return i */
				if ( live_vars(i) == NULL_VAL) return i		
				
			}
			
			/** Original eviction policy, random register eviction */
			/** val selected_reg = rdm.nextInt(REG_COUNT)
				DebugBreakpoint("Randomly selected reg is : " + selected_reg + ", and contains : " + CPU_regs(selected_reg) ) */
			
			
			/** Select most least recently used register to clear */
			val selected_reg = last_use.head

			/** Clear the reg */
			evict( selected_reg )
			
			DebugBreakpoint("Evicted, now contains : " + CPU_regs(selected_reg) )
			
			return selected_reg
			
		}
		
		/** Evict all registers back to RAM */
		def flush() : Unit = for (i <- 0 until CPU_regs.size ){ evict(i) }
		
		override def toString : String = {
		
			var s = "CPU REGs :\n"
		
			for (i <- 0 until CPU_regs.size ) {
			
				s += "[" + i + " : " + live_vars(i) + "] -> " + CPU_regs(i) + "\n"
			} 
		
			return s
		}
}