
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Scanner;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/***********************************************************************************************
 * Name: Eric J. Hachuel
 * CSCI 561 - Artificial Intelligence, Fall 2017 (Homework 3 - Logic Reasoning)
 * Algorithm Implemented: First-Order Logic Resolution
 ***********************************************************************************************/

/********************************************************************************
 * The interface Term class is used to implement the various components needed
 * for the homework such as Tuples, Constants/Predicates, and Variables
 ********************************************************************************/
interface Term{
    String getTermValue();
    boolean isTuple();
    boolean isConstant();
    boolean isVariable();
    List<Term> getParameters();
    Term copy();
    SubstitutionMap unify(Term term, SubstitutionMap subsMap);
    Term replaceVarBindings(SubstitutionMap subsMap);
}

/********************************************************************************
 * The Constant class represents First Order Logic Constants and implements
 * the term interface
 ********************************************************************************/
class Constant implements Term{
    
    private String constantName;
 
    /**
     * Constant constructor
     * @param name the name of the constant
     */
    public Constant(String name){
        this.constantName = name.trim();
    }
    
    /**
     * Getter method to retrieve Constant name
     * @return the Constant's name
     */
    public String getConstantName(){
        return this.constantName;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        Constant other = (Constant) obj;
        return this.getConstantName().equals(other.getConstantName());
    }
    
    @Override
    public int hashCode() {
        int hash = 7;
        hash = 71 * hash + this.getConstantName().hashCode();
        return hash;
    }
    
    @Override
    public String toString(){
        return this.constantName;
    }
    
    /***********************METHODS INHERITED FROM TERM***********************/
    @Override
    public SubstitutionMap unify(Term term, SubstitutionMap subsMap){
        //Check if term is the same constant: return map
        if(this.equals(term)){ 
            return subsMap;
        }
        //Check if term is an instance of variable and unify
        else if(term.isVariable()){
            return term.unify(this, subsMap);
        }
        else{
            //return null otherwise
            return null;
        } 
    }
    
    @Override
    public List<Term> getParameters(){
        return null;
    }
    
    @Override
    public Term replaceVarBindings(SubstitutionMap subsMap){
        return this;
    }
    
    @Override
    public String getTermValue(){
        return getConstantName();
    }
    
    @Override
    public boolean isTuple(){
        return false;
    }
    
    @Override
    public boolean isVariable(){
        return false;
    }
    
    @Override
    public boolean isConstant(){
        return true;
    }
    
    @Override
    public Constant copy(){
        return new Constant(constantName);
    }
}

/********************************************************************************
 * The Variable class represents First Order Logic Variables and implements
 * the Term interface
 ********************************************************************************/
class Variable implements Term{
    
    private String variableName;
    
    /**
     * Variable constructor
     * @param varName the name of the Variable
     */
    public Variable(String varName){
        this.variableName = varName.trim();
    }
    
    /**
     * Getter method to retrieve the name of the Variable
     * @return the Variable's name
     */
    public String getVariableName(){
        return variableName;
    }
    
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Variable other = (Variable) obj;
        return this.getVariableName().equals(other.getVariableName());
    }

    @Override
    public int hashCode() {
        int hash = 3;
        hash = 89 * hash + this.getVariableName().hashCode();
        return hash;
    }
  
    @Override
    public String toString(){
        return this.getVariableName();
    }
    
    /***********************METHODS INHERITED FROM TERM***********************/
    @Override
    public SubstitutionMap unify(Term term, SubstitutionMap subsMap){
        //Check if the two are equal variables, return the substitution
        if(this.equals(term)){
            return subsMap;
        }
        //Check if this variable is already binded to a term in the substitution
        //If it is, return the unification of its binding with the given Term
        else if(subsMap.isBound(this)){
            Term bindingTerm = subsMap.getBindingTerm(this);
            return bindingTerm.unify(term, subsMap);
        }
        else{
            //If the variable is not bound, and doesn't occur in Term term
            subsMap.bind(this, term);
            //Propagate subsitutions through Substitution Map Variables
            for (Variable var : subsMap.getSubsMap().keySet()) {
                subsMap.bind(var, subsMap.getBindingTerm(var).replaceVarBindings(subsMap));
            }
            return subsMap;
        }
    }
    
    @Override
    public Term replaceVarBindings(SubstitutionMap subsMap){
        //Check if (this) variable is already bound, if so, replace var bindings in its binding recursively
        if(subsMap.isBound(this)){
            Term bindingTerm = subsMap.getBindingTerm(this);
            return subsMap.getBindingTerm(this).replaceVarBindings(subsMap);
        }
        //If the variable is not bound, return copy of itself
        else{
            return this;
        }
    }
    
    @Override
    public List<Term> getParameters(){
        return null;
    }
    
    @Override
    public boolean isTuple(){
        return false;
    }
    
    @Override
    public boolean isVariable(){
        return true;
    }
    
    @Override
    public boolean isConstant(){
        return false;
    }
    
    @Override
    public String getTermValue(){
        return getVariableName();
    }
    
    @Override
    public Variable copy(){
        return new Variable(variableName);
    }
}


/********************************************************************************
 * The Tuple class represents Functions and Predicates in First Order Logic
 * The class implements the Term Interface
 ********************************************************************************/
class Tuple implements Term{
    
    private Constant functor;
    private ArrayList<Term> parameters = new ArrayList<>();
    
    /**
     * Tuple Constructor
     * @param functorName the name of the functor/predicate
     * @param termParameters the parameters of the tuple
     */
    public Tuple(Constant functorName, ArrayList<Term> termParameters){
        this.functor = functorName;
        this.parameters = termParameters;
    }
    
    /**
     * Getter method to get the number of parameters in the Tuple
     * @return the number of parameters
     */
    public int getNumParameters(){
        return parameters.size();
    }
    
    
    /**
     * Getter method to retrieve the name of the Tuple's functor
     * @return The Tuple's functor name
     */
    public String getFunctorName(){
        return functor.getConstantName();
    }
    
    /**
     * Getter method to retrieve parameter at specified index
     * @param index the index of the parameter
     * @return the parameter
     */
    public Term getParameter(int index){
        return parameters.get(index);
    }

    @Override
    public int hashCode() {
        int hash = 3;
        hash = 73 * hash + this.getFunctorName().hashCode();
        
        for (int i = 0; i < this.getNumParameters(); i++) {
            hash = 73 * hash + this.getParameter(i).hashCode();
        }
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Tuple other = (Tuple) obj;
        return this.getFunctorName().equals(other.getFunctorName()) && this.getParameters().equals(other.getParameters());
    }

    @Override
    public String toString(){
        String parameterString="";
        if(functor == null){
            return null;
        }
        else{
            parameterString+= getFunctorName()+"(";
            for(int i=0; i < getNumParameters(); i++){
                if(i == (getNumParameters() - 1)){
                    parameterString += getParameter(i)+")";
                }
                else{
                    parameterString += getParameter(i)+",";
                }
            }
        }
        return parameterString;
    }
    
    /***********************METHODS INHERITED FROM TERM***********************/
    @Override
    public SubstitutionMap unify(Term term, SubstitutionMap subsMap){
        if(this.equals(term)){
            return subsMap;
        }
        //Check if term is also a Tuple; if so check length, and iterate over parameters
        else if(term.isTuple()){
            Tuple termTuple = (Tuple) term;
            String termTuplePredicate = termTuple.getFunctorName();
            if(!(this.getNumParameters() == termTuple.getNumParameters()) || !(this.getFunctorName().equals(termTuplePredicate))){
                return null;
            }
            //Attempt to unify each parameter in (this) tuple with its counterpart
            for (int i = 0; i < this.getNumParameters(); i++) {
                subsMap = this.getParameter(i).unify(termTuple.getParameter(i), subsMap);
                if(subsMap == null){
                    return null;
                }
            }
            return subsMap;
        }
        else{
            return null;
        }
    }
    
    @Override
    public Term replaceVarBindings(SubstitutionMap subsMap){
        //For tuples, replace var bindings in all its terms recursively
        ArrayList<Term> bindedParameters = new ArrayList<>();
        ArrayList<Term> currentParams = new ArrayList<>(this.getParameters());
        //Loop over terms and bind the terms
        for (int i = 0; i < currentParams.size(); i++) {
            Term newBindedParam = currentParams.get(i).replaceVarBindings(subsMap);
            bindedParameters.add(newBindedParam);
        }
        //Return a new sentence with its parameters binded
        Constant bindedConstant = new Constant(this.functor.getConstantName());
        Tuple bindedTuple = new Tuple(bindedConstant, bindedParameters);
        return bindedTuple;
    }
    
    
    @Override
    public List<Term> getParameters(){
        return this.parameters;
    }
    
    @Override
    public String getTermValue(){
        return getFunctorName();
    }
    
    @Override
    public boolean isTuple(){
        return true;
    }
    
    @Override
    public boolean isVariable(){
        return false;
    }
    
    @Override
    public boolean isConstant(){
        return false;
    }
    
    @Override
    public Tuple copy(){
        //Copy parameters and return new tuple
        ArrayList<Term> newParameters = new ArrayList<>();
        for(int i = 0; i < parameters.size(); i++){
            newParameters.add(parameters.get(i));
        }
        Constant newFunctor = new Constant(this.getFunctorName());
        return new Tuple(newFunctor, newParameters);
    }
}


/********************************************************************************
 * The Literal class represents FOL Literals, containing a sign and a Term
 ********************************************************************************/
class Literal{
    
    private boolean literalSign;
    private Term literalTerm;
    
    /**
     * Literal Constructor
     * @param sign the sign of the literal
     * @param literal the Literal's Term
     */
    public Literal(boolean sign, Term literal){
        this.literalSign = sign;
        this.literalTerm = literal;
    }
    
    /**
     * Getter method to retrieve the sign of the Literal
     * @return returns the sign of the literal
     */
    public boolean getSign(){
        return literalSign;
    }
    
    /**
     * Getter method to retrieve the Term within the Literal
     * @return the Term
     */
    public Term getLiteral(){
        return literalTerm;
    }
    
    @Override
    public String toString(){
        if(literalSign){
            return getLiteral().toString();
        }
        else{
            return "~"+getLiteral().toString();
        }
    }

    @Override
    public int hashCode() {
        
        String signValue = "negative";
        if(this.getSign()){
            signValue = "positive";
        }
        
        int hash = 7;
        hash = 29 * hash + this.getLiteral().getTermValue().hashCode();
        hash += signValue.hashCode();
        
        List<Term> parameters = this.getLiteral().getParameters();
        
        for (int i = 0; i < parameters.size(); i++) {
            hash += 29 * hash + parameters.get(i).hashCode();
        }
        
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Literal other = (Literal) obj;
        if (this.getSign() != other.getSign()) {
            return false;
        }
        if (!Objects.equals(this.getLiteral().getTermValue(), other.getLiteral().getTermValue())) {
            return false;
        }
        if (!Objects.equals(this.getLiteral().getParameters(), other.getLiteral().getParameters())) {
            return false;
        }
        return true;
    }
    
    
    /**
     * Copy constructor
     * @return a new Literal object with the same member variable values
     */
    public Literal copy(){
        return new Literal(this.getSign(), this.getLiteral().copy());
    }
    
    
    /**
     * Method to replace the variable bindings within the Literal
     * @param subsMap the given substitution map {var/Term}
     * @return a new Literal with its variables replaced with respective bindings
     */
    public Literal replaceVarBindings(SubstitutionMap subsMap){
        //Create a a copy of the literal term, replace var bindings of its term
        Term bindedLitTerm = this.getLiteral().replaceVarBindings(subsMap);
        return new Literal(this.getSign(), bindedLitTerm);
    }
}


/********************************************************************************
 * The Clause class containts a set of (the disjunction of) Literals
 ********************************************************************************/
// implements Comparable<Clause>
class Clause implements Comparable<Clause>{

    private LinkedHashSet<Literal> axiomSet = new LinkedHashSet<>();
    //Store positive and negative literals
    private ArrayList<Literal> positiveLiterals = new ArrayList<>();
    private ArrayList<Literal> negativeLiterals = new ArrayList<>();
    
    /**
     * Clause constructor
     * @param literalSet the set of literals within the clause
     */
    public Clause(LinkedHashSet<Literal> literalSet){
        this.axiomSet = literalSet;
        //Store positive and negative values for future retrieval
        for (Literal literal : this.axiomSet) {
            if(literal.getSign()){
                positiveLiterals.add(literal);
            }
            else{
                negativeLiterals.add(literal);
            }
        }
    }
    
    /**
     * standardize Standardizes the Clause to allow for hashcode() and equals() to work as required
     * @return teh standardized Clause
     */
    public Clause standardize(){
        LinkedHashSet<Literal> newSet = new LinkedHashSet<>();
        HashMap<Variable, Variable> varAssignments = new HashMap<>();
        ArrayList<Literal> newSetList = new ArrayList<Literal>();
        //Index to keep track of variable names
        int index = 0;
        for (Literal literal : this.axiomSet) {
            Tuple literalTuple = (Tuple) literal.getLiteral().copy();
            boolean literalSign = literal.getSign();
            String predicate = literalTuple.getFunctorName();
            Constant newPredicate = new Constant(predicate);
            ArrayList<Term> parameters = new ArrayList<>();
            //Loop over term parameters and generate new, standardized ones
            for (int i = 0; i < literalTuple.getNumParameters(); i++) {
                Term currTerm = literalTuple.getParameter(i);
                if(currTerm.isVariable()){
                    Variable termVar = (Variable) currTerm;
                    if(varAssignments.containsKey(termVar)){
                        parameters.add(varAssignments.get(termVar).copy());
                    }
                    else{
                        String standardVarName = "x"+index;
                        Variable newVar = new Variable(standardVarName);
                        parameters.add(newVar);
                        varAssignments.put(termVar, newVar);
                        index++;
                    }
                }
                else{
                    parameters.add(currTerm);
                }
            }
            Tuple standardTuple = new Tuple(newPredicate.copy(), parameters);
            Literal standardLiteral = new Literal(literalSign, standardTuple);
            newSetList.add(standardLiteral);
        }
        //sort the new List
        LiteralComparator newComparator = new LiteralComparator();
        Collections.sort(newSetList, newComparator);
        newSet.addAll(newSetList);
        Clause standardClause = new Clause(newSet);
        return standardClause;
    }
    
    /**
     * The empty clause constructor
     */
    public Clause(){}
    
    /**
     * Getter method to retrieve the number of literals within the Clause
     * @return the number of Literals
     */
    public int getClauseSize(){
        return axiomSet.size();
    }
    
    /**
     * Getter method to retrieve the Set of Literals from the clause
     * @return the set of Literals
     */
    public LinkedHashSet<Literal> getLiterals(){
        return axiomSet;
    }
    
    /**
     * Getter method to retrieve the list of positive literals within the clause
     * @return the list of positive literals
     */
    public ArrayList<Literal> getPositiveTerms(){
        return positiveLiterals;
    }
    
    /**
     * Getter method to retrieve the number of positive literals
     * @return the number of positive literals
     */
    public int getNumPositiveTerms(){
        return positiveLiterals.size();
    }
    
    /**
     * Getter method to retrieve the list of negative literals within the clause
     * @return the list of negative literals
     */
    public ArrayList<Literal> getNegativeTerms(){
        return negativeLiterals;
    }
    
     /**
     * Getter method to retrieve the number of negative literals
     * @return the number of negative literals
     */
    public int getNumNegativeTerms(){
        return negativeLiterals.size();
    }
    
    /**
     * Method to check whether the Clause is empty
     * @return true iff the clause is empty
     */
    public boolean isEmpty(){
        return axiomSet.isEmpty();
    }
    
    @Override
    public String toString(){
        String axiomString = "{";
        Iterator clauseIterator = axiomSet.iterator();
        while(clauseIterator.hasNext()){
            Literal next = (Literal) clauseIterator.next();
            axiomString += next.toString() + " | ";
        }
        if(axiomString.length() > 3){
            return axiomString.substring(0, axiomString.length() - 2) + "}";
        }
        return axiomString + "}";
    }

    @Override
    public int hashCode() {
        int hash = 7;
        Clause hashClause = this.standardize();
        String hashStringClause = hashClause.toString();
        hash += 59 * hashStringClause.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Clause other = (Clause) obj;
        //Standardize clauses before calculating equality
        Clause standardThis = this.standardize();
        Clause standardOther = other.standardize();
        
        String standardThisString = standardThis.toString();
        String standardOtherString = standardOther.toString();
        
        if(standardThisString.length() == standardOtherString.length()){
            for(int i = 0; i < standardThisString.length(); i++){
                if(standardThisString.charAt(i) != standardOtherString.charAt(i)){
                    return false;
                }
            }
            return true;
        }
        return false;
    }
    
    /**
     * Copy constructor for the Clause
     * @return a new Clause with the same member variable values as (this)
     */
    public Clause copy(){
        Iterator clauseIterator = axiomSet.iterator();
        LinkedHashSet<Literal> newAxiomSet = new LinkedHashSet<Literal>();
        
        while(clauseIterator.hasNext()){
            Literal nextLiteral = (Literal) clauseIterator.next();
            Literal newLiteral = nextLiteral.copy();
            newAxiomSet.add(newLiteral);
        }
        return new Clause(newAxiomSet);
    }
    
    @Override
    public int compareTo(Clause otherClause){
        return (this.getClauseSize() - otherClause.getClauseSize());
    }
}

/********************************************************************************
 * The LiteralComparator class will allow us to compare and sort a list of
 * Literals, which will be essential for the proper functioning of the 
 * HashSet of Clauses. (see equals() and hashcode() functions)
 ********************************************************************************/
class LiteralComparator implements Comparator<Literal>{
    public int compare(Literal literal1, Literal literal2){
        int compareValue = 0;
       //We will compare literals by their sign first
       if(!literal1.getSign() && literal2.getSign()){
           //Sort negative literals first
           return -1;
       }
       else if(literal1.getSign() && !literal2.getSign()){
           return 1;
       }
       //if both literals have the same sign, compare the Term's predicate value
       //We know its terms are Tuple's
       String literal1Name = literal1.getLiteral().getTermValue();
       String literal2Name = literal2.getLiteral().getTermValue();
       
       compareValue = literal1Name.compareTo(literal2Name);
       
       if(compareValue != 0){
           return compareValue;
       }
       //If the two Tuple's names are the same, compare the arguments
       else{
           Tuple literal1Tuple = (Tuple) literal1.getLiteral();
           Tuple literal2Tuple = (Tuple) literal2.getLiteral();
           List<Term> parameters1 = literal1Tuple.getParameters();
           List<Term> parameters2 = literal2Tuple.getParameters();
           
           //Compare the size of the terms, return the one with most if not equal
           compareValue = parameters1.size() - parameters2.size();
           //if equal, compare arguments
           if(parameters1.size() == parameters2.size()){
               return compareLiteralTerms(parameters1, parameters2); 
           }
           else{
               return (parameters1.size() - parameters2.size());
           }
       }
    }
    
    public int compareLiteralTerms(List<Term> parameterList1, List<Term> parameterList2){
        int compareValue = 0;
        //Only variables or constants inside the Tuples (homework prompt)
        //Variables will be given precedence
        for(int i = 0; i < parameterList1.size(); i++){
            //compare paramater to parameter
            Term currParameterList1 = parameterList1.get(i);
            Term currParameterList2 = parameterList2.get(i);
            //if both paramteres are constants, compare their names
            if(currParameterList1.isConstant() && currParameterList2.isConstant()){
                compareValue = currParameterList1.getTermValue().compareTo(currParameterList2.getTermValue());
                if(compareValue != 0){
                    if(currParameterList1.isConstant()){
                        compareValue = 1;
                    }
                    else{
                        compareValue = -1;
                    }
                    return compareValue;
                }
            }
        }
        return compareValue;
    }
}

/********************************************************************************
 * The Substitution class represents the Substitution Map of Variables to Terms
 * Represented as a HashMap
 ********************************************************************************/
class SubstitutionMap{

    private HashMap<Variable, Term> substitutionMap = new HashMap<>();
    
    /**
     * Substitution Map Constructor
     * @param substitution the Substitution Map
     */
    public SubstitutionMap(SubstitutionMap subsMap){
        this.substitutionMap = new HashMap<Variable, Term>(subsMap.substitutionMap);
    }
    
    /**
     * Empty Substitution Map constructor
     */
    public SubstitutionMap(){}
    
    /**
     * Method to bind a variable to a term
     * @param var the variable to bind
     * @param term the term to bind the variable to
     */
    public void bind(Variable var, Term term){
        substitutionMap.put(var, term);
    }
    
    /**
     * Method to check whether a specific variable is bound within the Map
     * @param var the variable
     * @return true iff variable var is bound
     */
    public boolean isBound(Variable var){
        return substitutionMap.get(var) != null;
    }
    
    /**
     * Method to retrieve the term the variable is bound to
     * @param var the variable
     * @return the binding term of variable var
     */
    public Term getBindingTerm(Variable var){
        return (Term) substitutionMap.get(var);
    }
    
    /**
     * Method to retrieve the Map within the Substitution class
     * @return the HashMap of {var/Term} values
     */
    public Map<Variable, Term> getSubsMap(){
        return this.substitutionMap;
    }
    
    public boolean isEmpty(){
        return this.substitutionMap.isEmpty();
    }
    
    @Override
    public String toString(){
        return substitutionMap.toString();
    }  
}


/********************************************************************************
 * The homework class is the "main" class of the homework (the only public class)
 * It contains the main function
 ********************************************************************************/
public class homework {
    private static final double TOTAL_RES_TIME = 20000;
    private static final String NOT_ENTAILED = "FALSE";
    private static final String ENTAILED = "TRUE";
    //Index for variable standardization
    private static int currentIndex;
    
    /**
     * negateQuery negates the input query (removes or adds '~' as required)
     * @param query the input query (from input.txt)
     * @return the negated query
     */
    public static String negateQuery(String query){
        String negatedQuery = "";
        if(query.charAt(0) == '~'){
            negatedQuery = query.substring(1);
        }
        else{
            negatedQuery = '~' + query;
        }
        return negatedQuery;
    }
    
    /**
     * Code to standardize Clause from KB
     * @param originalClause the clause you want to standardize
     * @return the standardized Clause
     */
    public static Clause standardizeClause(Clause originalClause){
        currentIndex++;
        SubstitutionMap standardizedMap = new SubstitutionMap();
        //Store all the variables from the clause n a HashSet
        HashSet<Variable> originalVariableSet = new HashSet<>();
        //Get the literal set from the clause
        LinkedHashSet<Literal> clauseLiteralSet = originalClause.getLiterals();
        //Gather all the variables
        for (Literal orgLiteral : clauseLiteralSet) {
            //Every Literal is formed by a tuple
            Tuple literalTuple = (Tuple) orgLiteral.getLiteral();
            //Loop through parameters to find variables
            for(int i = 0; i < literalTuple.getNumParameters(); i++){
                //If the parameter is a variable, add it to the variable set
                if(literalTuple.getParameter(i).isVariable()){
                    originalVariableSet.add( (Variable) literalTuple.getParameter(i));
                }
            }
        }
        //Loop through the variable set, standardize each value
        for (Variable orgVariable : originalVariableSet) {
            if(orgVariable.getVariableName().length() > 1){
                Variable standardizedVar = new Variable(orgVariable.getVariableName().substring(0, 1) + currentIndex);
                //Add the new variable and its substitution to the map
                standardizedMap.bind(orgVariable, standardizedVar);
            }
            else{
                Variable standardizedVar = new Variable(orgVariable.getVariableName() + currentIndex);
                //Add the new variable and its substitution to the map
                standardizedMap.bind(orgVariable, standardizedVar);
            }
        }
        //Use the new bindings to substitute variables and generate a new clause
        if(!standardizedMap.isEmpty()){
            LinkedHashSet<Literal> standardizedLiteralSet = new LinkedHashSet<>();
            //Loop through the original literals, replace variables and add to new set
            for (Literal literal : clauseLiteralSet) {
                Literal newLiteral = literal.replaceVarBindings(standardizedMap);
                standardizedLiteralSet.add(newLiteral);
            }
            Clause standardizedClause = new Clause(standardizedLiteralSet);
            return standardizedClause;
        }
        return originalClause;
    }
    
    /**
     * Resolve takes in two Clauses and generates a HashSet of resulting knowledge as Clauses
     * @param outerClause Clause to be resolved
     * @param innerClause Clause to be resolved 
     * @return the Set of all new knowledge acquired through the two given clauses
     */
    public static LinkedHashSet<Clause> resolve(Clause outerClause, Clause innerClause){
        //Instantiate the resolvents set
        LinkedHashSet<Clause> resolventsSet = new LinkedHashSet<>();
        //Array of all items
        ArrayList<Literal> allLiterals = new ArrayList<>();
        //Get positive and negative terms from poth clauses for subsequent loops
        allLiterals.addAll(outerClause.getPositiveTerms());
        allLiterals.addAll(innerClause.getPositiveTerms());
        allLiterals.addAll(outerClause.getNegativeTerms());
        allLiterals.addAll(innerClause.getNegativeTerms());
        //We must resolve positive literals of the outerClause with negative of the innerClause
        //We must also resolve positive literals of the innerClause with negative of the outerClause
        ArrayList<Literal> positiveLiteralsOuter = new ArrayList<>(outerClause.getPositiveTerms());
        ArrayList<Literal> negativeLiteralsInner = new ArrayList<>(innerClause.getNegativeTerms());
        ArrayList<Literal> negativeLiteralsOuter = new ArrayList<>(outerClause.getNegativeTerms());
        ArrayList<Literal> positiveLiteralsInner = new ArrayList<>(innerClause.getPositiveTerms());    
        //Resolve positive outer with negative inner
        for (int posOuter = 0; posOuter < positiveLiteralsOuter.size(); posOuter++) {
            for (int negInner = 0; negInner < negativeLiteralsInner.size(); negInner++) {
                //Create a new substitution map for each unification attempt
                SubstitutionMap resolveMap = new SubstitutionMap();
                //Get the Terms and attempt unification
                Term outerPosTerm = positiveLiteralsOuter.get(posOuter).getLiteral();
                Term innerNegTerm = negativeLiteralsInner.get(negInner).getLiteral();
                //if the attempted substitution is not null, propagate
                if(outerPosTerm.unify(innerNegTerm, resolveMap) != null){
                    LinkedHashSet<Literal> resLiteralSet = new LinkedHashSet<>();
                    ArrayList<Literal> resLiteralList = new ArrayList<>();
                    //Loop through all literals, add all items to new list (except unified terms)
                    for (int allLitsIndex = 0; allLitsIndex < allLiterals.size(); allLitsIndex++) {
                        //If the current literal is not one of the unified terms, add it with its bindings replaced 
                        if(!(allLiterals.get(allLitsIndex).equals(positiveLiteralsOuter.get(posOuter))) && !(allLiterals.get(allLitsIndex).equals(negativeLiteralsInner.get(negInner)))){
                            resLiteralList.add(allLiterals.get(allLitsIndex).replaceVarBindings(resolveMap));
                        }
                    }
                    //Sort the list and add to hashset
                    LiteralComparator newComparator = new LiteralComparator();
                    Collections.sort(resLiteralList, newComparator);
                    resLiteralSet.addAll(resLiteralList);
                    //Create new Cluase with the literal set
                    Clause resolventClause = new Clause(resLiteralSet);
                    Clause standardizedClause = standardizeClause(resolventClause);
                    resolventsSet.add(standardizedClause);
                }
            }
        }
        //Resolve negative outer with positive inner
        for (int negOuter = 0; negOuter < negativeLiteralsOuter.size(); negOuter++) {
            for (int posInner = 0; posInner < positiveLiteralsInner.size(); posInner++) {
                //Create a new substitution map for each unification attempt
                SubstitutionMap resolveMap = new SubstitutionMap();
                //Get the Terms and attempt unification
                Term outerNegTerm = negativeLiteralsOuter.get(negOuter).getLiteral();
                Term innerPosTerm = positiveLiteralsInner.get(posInner).getLiteral();
                //if the attempted substitution is not null, propagate
                if(outerNegTerm.unify(innerPosTerm, resolveMap) != null){
                    LinkedHashSet<Literal> resLiteralSet = new LinkedHashSet<>();
                    ArrayList<Literal> resLiteralList = new ArrayList<>();
                    //Loop through all literals, add all items to new list (except unified terms)
                    for (int allLits = 0; allLits < allLiterals.size(); allLits++) {
                        //If the current literal is not one of the unified terms, add it with its bindings replaced 
                        if(!(allLiterals.get(allLits).equals(negativeLiteralsOuter.get(negOuter))) && !(allLiterals.get(allLits).equals(positiveLiteralsInner.get(posInner)))){
                            resLiteralList.add(allLiterals.get(allLits).replaceVarBindings(resolveMap));
                        }
                    }
                    //Sort the list and add to hashset
                    LiteralComparator newComparator = new LiteralComparator();
                    Collections.sort(resLiteralList, newComparator);
                    resLiteralSet.addAll(resLiteralList);
                    //Create new Cluase with the literal set
                    Clause resolventClause = new Clause(resLiteralSet);
                    Clause standardizedClause = standardizeClause(resolventClause);
                    resolventsSet.add(standardizedClause);
                }
            }
        }
        return resolventsSet;
    }
    
    /**
     * The Resolution method
     * @param knowledgeBase the standardized (KB^~alpha) knowledge base
     * @return true iff the Knowledge Base entails alpha (KB |= alpha)
     */
    public static boolean resolution(LinkedHashSet<Clause> knowledgeBase){
        //Track time to kill infinite loops
        double startTime = System.currentTimeMillis();
        //Initiate do-loop to find resolvents for each pair of clauses in the KB
        do{
            //Create the 'new' set
            LinkedHashSet<Clause> newSet = new LinkedHashSet<>();
            //ArrayList for iterating
            ArrayList<Clause> kbArrayList = new ArrayList<>();
            kbArrayList.addAll(knowledgeBase);
            Collections.sort(kbArrayList);
            for(int i = 0; i < kbArrayList.size() - 1; i++){
                Clause outerClause = kbArrayList.get(i);
                for(int j = i + 1; j < kbArrayList.size(); j ++){
                    Clause innerClause = kbArrayList.get(j);
                    ArrayList<Literal> outerLiterals = new ArrayList<>(outerClause.getLiterals());
                    ArrayList<Literal> innerLiterals = new ArrayList<>(innerClause.getLiterals());
                    boolean validCombo = false;
                    //MAKE INTO ARRAYLISTS
                    //Check whether unification is viable between these two clauses
                    for (int outer = 0; outer < outerLiterals.size(); outer++) {
                        for (int inner = 0; inner < innerLiterals.size(); inner++) {
                            if(outerLiterals.get(outer).getLiteral().getTermValue().equals(innerLiterals.get(inner).getLiteral().getTermValue())){
                                if(outerLiterals.get(outer).getSign() != innerLiterals.get(inner).getSign()){
                                    validCombo = true;
                                }
                            } 
                        } 
                    }
                    //If the combination is potentially valid (i.e complementary predicates found) run resolve
                    if(validCombo){
                        //Instantiate the Resolvents LinkedHashSet and call resolve
                        LinkedHashSet<Clause> resolventsSet = new LinkedHashSet<>();
                        /***********************RESOLVE***********************/
                        resolventsSet = resolve(outerClause, innerClause);
                        int resolventSetSize = resolventsSet.size();
                        if(resolventSetSize > 0){
                            for (Clause clause : resolventsSet) {
                                if(clause.isEmpty()){
                                    return true;
                                }
                            }
                            //new U resolvents
                            newSet.addAll(resolventsSet);
                        }
                    }
                    double currTime = System.currentTimeMillis();
                    if((currTime - startTime) > TOTAL_RES_TIME){
                        return false;
                    }
                }
            }
            //Check if new is a subset of clauses
            //if new is a subset of clauses in the KB, return false
            if(knowledgeBase.containsAll(newSet)){
                return false;
            }
            //Add the new set to the knowledge base and loop
            knowledgeBase.addAll(newSet);
        } while (true);
    }
    
    
    /**
     * Creates the output file with the answers
     * @param answersList the answer to the ASK question to the KB
     */
    public static void printOutFile(ArrayList<String> answersList){
        PrintStream outputFileStream = null;
        try {
            outputFileStream = new PrintStream( new FileOutputStream("output.txt"));
        } catch (FileNotFoundException ex) {
            Logger.getLogger(homework.class.getName()).log(Level.SEVERE, null, ex);
        }
        for(int i = 0; i < answersList.size(); i++){
            outputFileStream.println(answersList.get(i));
        }
    }
    
    
    public static void printKB(LinkedHashSet<Clause> knowledgeBase){
        System.out.println("---------KB PRINTER---------");
        ArrayList<Clause> clauseList = new ArrayList<>();
        clauseList.addAll(knowledgeBase);
        Collections.sort(clauseList);
        LinkedHashSet<Clause> clausePrint = new LinkedHashSet<>();
        clausePrint.addAll(clauseList);
        
        Iterator kbIterator = clausePrint.iterator();
        while(kbIterator.hasNext()){
            System.out.println(kbIterator.next());
        }
    }
    
    
    public static void main(String[] args) {
        //Arraylist to store answers to different queries (i.e. TRUE, FALSE, TRUE, etc.)
        ArrayList<String> answersList = new ArrayList<String>();
        //Initialize the KB
        LinkedHashSet<Clause> knowledgeBase = new LinkedHashSet<>();
        //Pattern Objet for parsing sentences
        String regexElement = "[A-Za-z]+";
        Pattern regexPattern = Pattern.compile(regexElement);
        Matcher patternMatcher;
        try {
            //Read the input file containing the input resolution problem in the current directory
            File InputFile = new File("input.txt");
            Scanner inputReader = new Scanner(InputFile);
            //Stores the next int as the subsequent number of queries to ASK the KB
            int numQueries = inputReader.nextInt();
            //Consume line and store the querie(s)
            inputReader.nextLine();
            String[] negatedQueryList = new String[numQueries];
            //Fill queryList array with queries from problem definition after negating them
            for(int i = 0; i < numQueries; i++){
                negatedQueryList[i] = negateQuery(inputReader.nextLine());
            }
            //Stores the next int as the subsequent number of sentences to tell the KB
            int numSentences = inputReader.nextInt();
            //Consume line and store the sentence(s)
            inputReader.nextLine();
            String[] sentenceArray = new String[numSentences];
            //Fill sentenceList array with sentences from problem definition 
            for(int i = 0; i < numSentences; i++){
                sentenceArray[i] = inputReader.nextLine();
            }
            //Parse each sentence, apply regex patterns, create instances of classes as required
            for(int sentenceNumber = 0; sentenceNumber < sentenceArray.length; sentenceNumber++){
                String sentence = sentenceArray[sentenceNumber];
                String sentenceNoSpaces = sentence.replaceAll("\\s+", "");
                //Split sentences by "OR" delimiter
                String[] delimiterSplitSentences = sentenceNoSpaces.split("\\|");
                //Instantiate HashSet to store each sentence as a Clause
                Clause newClause = null;
                LinkedHashSet<Literal> literalSet = new LinkedHashSet<>();
                //Use Regex to analyze each literal of the split sentence
                for(int j = 0; j < delimiterSplitSentences.length; j++){
                    String currentLiteral = delimiterSplitSentences[j];
                    boolean literalSign = currentLiteral.charAt(0) != '~';
                    //Instantiate arraylist to store parameters of literal
                    ArrayList<Term> currentParameters = new ArrayList<>();
                    //ArrayList to store the atomic elements from each delimited Literal
                    ArrayList<String> atomicElementsArray = new ArrayList<>();
                    //Pattern Matcher
                    patternMatcher = regexPattern.matcher(currentLiteral);
                    while(patternMatcher.find()){
                        String atomicItem = currentLiteral.substring(patternMatcher.start(),patternMatcher.end());
                        atomicElementsArray.add(atomicItem);
                    }
                    //Initialize tuple and predicate
                    Tuple currentTuple = null;
                    Constant predicate = null;
                    //Loop through atomic elements Array of current literal and generate appropriate classes
                    for(int k = 0; k < atomicElementsArray.size(); k++){
                        //Get the first item
                        String currentAtom = atomicElementsArray.get(k);
                        //First element is always a functor/predicate
                        if(k == 0){
                            predicate = new Constant(currentAtom);
                        }
                        else{
                            if(Character.isUpperCase(currentAtom.charAt(0))){
                                Constant constant = new Constant(currentAtom);
                                currentParameters.add(constant);
                            }
                            else{
                                //Add the index to the variable name to ensure standardization of variables
                                Variable variable = new Variable(currentAtom);
                                currentParameters.add(variable);
                            }
                        }
                    }
                    //Create a tuple with the parsed information
                    currentTuple = new Tuple(predicate, currentParameters);
                    //Generate new Literal and add it to the Clause Set
                    Literal newLiteral = new Literal(literalSign, currentTuple);
                    //Add new Literal to Clause Set
                    literalSet.add(newLiteral);
                }
                //Generate new clause and add it to the KB
                newClause = new Clause(literalSet);
                knowledgeBase.add(newClause);
            }
            /***********************MAIN LOOP (ADD QUERY AND RESOLVE)***********************/
            for(int queryNumber = 0; queryNumber < negatedQueryList.length; queryNumber++){
                //Index used to standardize variables in KB
                currentIndex = 1;
                //Create a new KB
                LinkedHashSet<Clause> newKB = new LinkedHashSet<>();
                //Iterator for the current knowledge base
                Iterator kbIterator = knowledgeBase.iterator();
                
                /***********************ADD (~ALPHA) TO THE NEW KB***********************/
                //Add the negated query to the new KB (no need to standardize)
                String currentQuery = negatedQueryList[queryNumber];
                boolean currQuerySign = currentQuery.charAt(0) != '~';
                //Pattern Matcher
                patternMatcher = regexPattern.matcher(currentQuery);
                //find next item: Always a predicate (as specified in hw prompt)
                patternMatcher.find();
                Constant queryPredicate = new Constant(currentQuery.substring(patternMatcher.start(),patternMatcher.end()));
                //find next item: Always a single/list constant (as specified in hw prompt)
                ArrayList<Term> queryConstantList = new ArrayList<>();
                while(patternMatcher.find()){
                    Constant queryConstant = new Constant(currentQuery.substring(patternMatcher.start(),patternMatcher.end()));
                    queryConstantList.add(queryConstant);
                }
                //Create the Tuple, Literal, and add 
                Tuple queryTuple = new Tuple(queryPredicate, queryConstantList);
                Literal queryLiteral = new Literal(currQuerySign, queryTuple);
                LinkedHashSet<Literal> queryLiteralSet = new LinkedHashSet<>();
                queryLiteralSet.add(queryLiteral);
                Clause queryClause = new Clause(queryLiteralSet);
                //Add the query clause to the new KB
                newKB.add(queryClause);
                /***********************GENERATE KB AND STANDARDIZE ON THE GO***********************/
                //Iterate over the current knowledge base, standardize, add to new one.
                while(kbIterator.hasNext()){
                    Clause currentClause = (Clause) kbIterator.next();
                    LinkedHashSet<Literal> refLiteralSet = currentClause.getLiterals();
                    LinkedHashSet<Literal> newLiteralSet = new LinkedHashSet<>();
                    //Iterator to iterate over each clause in the KB
                    Iterator clauseIterator = refLiteralSet.iterator();
                    while(clauseIterator.hasNext()){
                        //Get the current Literal and its sign
                        Literal currLiteral = (Literal) clauseIterator.next();
                        boolean currSign = currLiteral.getSign();
                        //Get the current Tuple within the Literal Object
                        Tuple currTuple = (Tuple) currLiteral.getLiteral();
                        String newPredicate = currTuple.getFunctorName();
                        //Create a new ArrayList to store the copied and standardized parameters
                        ArrayList<Term> newParameters = new ArrayList<>();
                        //Loop over Tuple's parameters
                        for (int i = 0; i < currTuple.getNumParameters(); i++) {
                            //Get the name of the current parameter Term
                            String termValue = currTuple.getParameter(i).getTermValue();
                            //Create a constant if the Parameter starts with an uppercase letter
                            if(Character.isUpperCase(termValue.charAt(0))){
                                Constant newConstant = new Constant(termValue);
                                newParameters.add(newConstant);  
                            }
                            //Otherwise, create a variable and add the index (sentence number) for standardizing
                            else{
                                //Add the index to the variable name to ensure standardization of variables
                                Variable variable = new Variable(termValue + currentIndex);
                                newParameters.add(variable);
                            }
                        }
                        //Create a new literal with the current sign and a new tuple containing a new predicate and the new parameters
                        Literal newLiteral = new Literal(currSign, new Tuple(new Constant(newPredicate), newParameters));
                        //Add the new literal to the set
                        newLiteralSet.add(newLiteral);
                    }
                    //Create a new clause with the new literal set and add the Clause to the KB
                    Clause newClause = new Clause(newLiteralSet);
                    newKB.add(newClause);
                    //Increment the index (used for variable standardization)
                    currentIndex++;
                }
                /***********************RUN RESOLUTION AND OUTPUT RESULTS***********************/
                boolean resolutionAnswer = resolution(newKB);
                if(resolutionAnswer){
                    answersList.add(ENTAILED);
                    System.out.println(ENTAILED);
                }
                else{
                    answersList.add(NOT_ENTAILED);
                    System.out.println(NOT_ENTAILED);
                }
            }
            /***********************PRINT OUTPUT FILE***********************/
            printOutFile(answersList);
            

        } catch (FileNotFoundException ex) {
            Logger.getLogger(homework.class.getName()).log(Level.SEVERE, null, ex);
        }
    }
}
