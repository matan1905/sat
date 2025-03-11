fs = require('fs')

function main(){

    const fileName = process.argv[2].endsWith('.dimacs') ? process.argv[2] : process.argv[2]+'.dimacs'
    const file = fs.readFileSync(__dirname+'/'+fileName).toString()
    let clauses = (file).split('\n').map(x=>x.split(/\s+/).sort((a,b)=>{
        return a.replace('-','').localeCompare(b.replace('-',''))
    }).slice(1))

    let firstLen = clauses.length
    let lastLen = clauses.length
    do {
        firstLen = clauses.length
        clauses = optimize(clauses)
        const ps2 = pseudoSat2(clauses)
        if(ps2.finalAssignments.length > 0){
            for (let assign of ps2.finalAssignments) {
                clauses = setVariable(clauses,clean(assign),!isNeg(assign))
            }
        }
        lastLen = clauses.length
    } while (lastLen !== firstLen)
    console.log(clauses)
}

// like var or not but instead of merging the vars it keeps them (a b c)(a y z)(...) => ((b c) | (y z))(...)
function pseudoSat2(clauses) {
    let stack = [clauses]; // Stack to simulate recursion
    let result = [];
    const finalAssignments = []

    function optimizeClauses(result, currentClauses) {
        const assignments = new Set(); // Track all assigned values

        while (true) {
            let newAssignments = []; // Stores newly discovered assignments

            // Process the result for direct assignments
            if (result.length > 0) {
                const newResult = [];
                for (let i = 0; i < result.length; i++) {
                    let [part1, part2] = result[i];

                    const isPart1False = part1.length === 0 || part1.some(x => x.length === 0);
                    const isPart2False = part2.length === 0 || part2.some(x => x.length === 0);

                    if (isPart1False && !isPart2False) {
                        if (part2.every(x => x.length === 1)) {
                            finalAssignments.push(part2[0][0]);
                            newAssignments.push(part2[0][0]); // Collect assignment
                            continue; // Do not push to currentClauses
                        }
                        currentClauses.push(...part2);
                        continue;
                    } else if (isPart2False && !isPart1False) {
                        if (part1.every(x => x.length === 1)) {
                            newAssignments.push(part1[0][0]); // Collect assignment
                            finalAssignments.push(part1[0][0]); // Collect assignment
                            continue; // Do not push to currentClauses
                        }
                        currentClauses.push(...part1);
                        continue;
                    } else if (isPart1False && isPart2False) {
                        throw "unsat"
                    }

                    newResult.push([part1, part2]);
                }
                result = newResult;
            }

            // **Check for unit clauses in `currentClauses`**
            let remainingClauses = [];
            for (let clause of currentClauses) {
                if (clause.length === 1) {
                    let unit = clause[0]; // Single literal to be assigned
                    if (!assignments.has(unit)) {
                        console.log("assign", [unit]);
                        newAssignments.push(unit);
                        finalAssignments.push(unit);
                    }
                } else {
                    remainingClauses.push(clause);
                }
            }
            currentClauses = remainingClauses; // Remove identified unit clauses

            // **If no new assignments, break the loop**
            if (newAssignments.length === 0) break;

            // **Process assignments and simplify**
            for (let assigned of newAssignments) {
                let negAssigned = assigned.startsWith('-') ? assigned.slice(1) : `-${assigned}`;

                if (assignments.has(negAssigned)) {
                    throw new Error("UNSAT"); // Conflict detected
                }

                assignments.add(assigned);

                // Remove satisfied clauses & unit propping removals
                currentClauses = currentClauses
                    .filter(clause => !clause.includes(assigned)) // Remove satisfied clauses
                    .map(clause => clause.filter(lit => lit !== negAssigned)); // Remove negations from remaining clauses

                // Apply assignment to `result` **properly**
                result = result.map(([p1, p2]) => [
                    p1.filter(clause => !clause.includes(assigned)).map(clause => clause.filter(lit => lit !== negAssigned)),
                    p2.filter(clause => !clause.includes(assigned)).map(clause => clause.filter(lit => lit !== negAssigned))
                ]);

            }

            // **Restart loop to propagate assignments**
        }
        return {result,currentClauses};
    }
    while (stack.length > 0) {
        let currentClauses = stack.pop();
        if (currentClauses.length === 0) continue; // Skip empty sets

        // First check for assignments
        // const assign = currentClauses.find(clause=> clause.length === 1);
        // if(assign){
        //     assigments[clean(assign[0])] = sign(assign[0]);
        //     console.log("@",assigments)
        //     break;
        // }

        // Count frequency of each variable (ignoring signs)
        let varCount = new Map();
        currentClauses.forEach(clause => {
            clause.forEach(variable => {
                let plainVar = variable.replace('-', '');
                varCount.set(plainVar, (varCount.get(plainVar) || 0) + 1);
            });
        });

        if (varCount.size === 0) continue; // No more variables left to process

        // Find the most used variable
        let mostUsedVar = [...varCount.entries()].reduce((a, b) => b[1] > a[1] ? b : a)[0];

        let f1 = [], f2 = [], f3 = [];

        // Partition clauses
        currentClauses.forEach(clause => {
            if (clause.includes(mostUsedVar)) {
                f1.push(clause.filter(v => v !== mostUsedVar)); // Remove positive occurrence
            } else if (clause.includes('-' + mostUsedVar)) {
                f2.push(clause.filter(v => v !== '-' + mostUsedVar)); // Remove negative occurrence
            } else {
                f3.push(clause); // Clause does not contain the variable
            }
        });



        // Merge f1 or f2 into f3 if the other is empty
        // if (f1.length === 0 && f2.length > 0) {
        //     f3.push(...f2);
        //     f2 = [];
        // } else if (f2.length === 0 && f1.length > 0) {
        //     f3.push(...f1);
        //     f1 = [];
        // }

        // Append [[f1, f2]] if they still exist
        if (f1.length > 0 || f2.length > 0) {
            result.push([f1, f2]);
        }

        const optimized = optimizeClauses(result,f3)
        result = optimized.result
        f3 = optimized.currentClauses

        // Push optimized f3 to stack for further processing
        if (f3.length > 0) {
            stack.push(f3); // Apply optimization before adding to stack
        }
    }


    return {result,finalAssignments};
}



// Removes a single variable from the clauses using the fact that if we have (a x)(a' y) then (x y)
// for example if we have F = (a x)(a' y)(b c) then we can seperate to positive form, negative form and neither
// then we can take all the positive and add to all the negative and finally merge back => (x y)(b c)
// this is unsat when there is an empty clause being generated.
function VarOrVarNot(clauses){
    // clauses = optimize(clauses)
    // remove duplicates extreamly fast

    const varCount = getVarCount(clauses)
    const varCountKeys = Object.keys(varCount)
    // Lowest count first
    const sortedVars =varCountKeys.sort((a,b)=>{
        return varCount[a]*varCount[not(a)]-varCount[b]*varCount[not(b)]
    })

    const leastFrequentVar = sortedVars[0]
    // split between clauses with and without the least frequent var
    const clausesWithVar = []
    const clausesWithoutVar = []
    for(let clause of clauses){
        if(clause.find(v=>clean(v)===(leastFrequentVar))){
            clausesWithVar.push(clause)
        } else {
            clausesWithoutVar.push(clause)
        }
    }

    // Split between true and false
    const trueClauses = []
    const falseClauses = []
    for(let clause of clausesWithVar){

        if(clause.find(v=>v===leastFrequentVar)){
            trueClauses.push(clause.filter(v=>clean(v)!==leastFrequentVar))
        } else {
            falseClauses.push(clause.filter(v=>clean(v)!==leastFrequentVar))
        }
    }
    let newClauses = []
    for(let trueClause of trueClauses){
        for(let falseClause of falseClauses){
            // true: (a | b) , false: (c | d) then (a | b | c | d)
            const raw = [...trueClause,...falseClause]
            const combined = raw.filter((v,i)=>raw.indexOf(v)===i) // remove duplicates
            // if a and not a is in the same clause, then the clause is always true, so we can ignore it
            if(raw.length===0) throw new Error('Unsatisfiable')
            if(!combined.find(v=>combined.includes(not(v)))){
                newClauses.push(combined)
            }

        }
    }


    return [...clausesWithoutVar,...newClauses]
}

function convertFalseToTrueByAddingVariablesAndXor(clauses){
    let varCount = Object.keys(getVarCount(clauses)).length
    let newClauses = []
    const varsAndOpposite = {}

    for (const clause of clauses) {
        const newClause = []
        for (const variable of clause) {
            if(!variableValue(variable)){
                if(!varsAndOpposite[variable]) varsAndOpposite[variable] = `${++varCount}`
                newClause.push(varsAndOpposite[variable])
            }else{
                newClause.push(variable)
            }
        }
        newClauses.push(newClause.map(x=>not(x)))
    }
    Object.entries(varsAndOpposite).forEach(([key,value])=>{
        newClauses.push([key,not(value)])
    })
    Object.entries(varsAndOpposite).forEach(([key,value])=>{
        newClauses.push([not(key),value])
    })


    // console.log(newClauses)
    console.log(newClauses.map(x=>x.join(' ')).join(' 0\n') + ' 0')

}


function clausesToDimacs(clauses){
    return clauses.map(x=>x.join(' ')).join(' 0\n') + ' 0'

}





function reOrderByImpact(clauses){
    const impact = {}
    for (let clause of clauses) {
        const key = clause.map(v=>Number(clean(v))).sort().join(' ')
            if(!impact[key]) impact[key]=0
            impact[key]++
    }
    console.log(impact)
    return clauses.sort((a,b)=>{
        return impact[b]-impact[a]
    })

}



function solveByAddingInformation(clauses){
    /*
    Assume that you have (a b)(a b')(a' b)
if you assign ab, then either:
1. that is a correct assignment
in that case, you can continue as usual and you just removed those variables


2. that is an incorrect assignment
if it is incorrect assignment, you can add the opposite of it - (a' b') to the clauses
but - oh, what's that? is that a.... unsat?

Selection:
starting with direct "killers" - any combination where adding the opposite will declare something as unsat.
followed by lowest caluse force optimizing (given a b c try a b c') - ordered by highest impact
     */
    // console.log(clauses)
    clauses = optimize(clauses)
    // console.log(clauses)
    // pick the first clause and negate one of the variables, as this is the only sure clause that isn't there
    // its noting the first var so when we repeat this a few times the issue is that it just nots a not and it loops
    if(clauses.length===0) return console.log('SAT')
    const clauseOg = clauses.shift()
    // console.log('og',clauseOg)
    const clause = [clauseOg.shift(),...clauseOg.map(v=>not(v))]
    // console.log('assuming',clause, clauses)
    // set it
    try {
        let copy = JSON.parse(JSON.stringify(clauses))
        for (let variable of clause) {
            copy = setVariable(copy,variable,variableValue(variable))
        }
        solveByAddingInformation(copy)

    } catch (e) {
        // add that clause to the clauses and try again
        // console.log('unsat. setting',clauseOg)
        clauses.unshift(clauseOg)
        // console.log('added',clause.map(v=>not(v)))
        solveByAddingInformation(clauses)
    }




}

function createClauseThatIsNotInClauses(clauses){
    let notTheBestClause=undefined
    // const chosenClause = clauses[Math.floor(Math.random()*clauses.length)]
    // find shortest one
    const chosenClause = clauses.reduce((acc,clause)=>{
        if(acc===undefined) return clause
        if(clause.length<acc.length) return clause
        return acc
    })
    for(let i = 2**chosenClause.length-1; i>0; i--){
       // perform a not equal to the i bits
        const clause = []
        for (let j = 0; j < chosenClause.length; j++) {
            const graycode = j ^ (j >> 1)
            if(i & (1<<graycode)){
                clause.push(not(chosenClause[j]))
            } else {
                clause.push(chosenClause[j])
            }
        }
        if(!clauses.find(c=>sameClause(c,clause))){
            if(!clauses.find(c=>sameClause(c,clause.map(v=>not(v))))){
                return clause
            } else {
                notTheBestClause = clause
            }
        }
    }
    if(notTheBestClause) return notTheBestClause
    console.log('unsatisfiable')
    throw new Error('Unsatisfiable')


}





/*
This idea comes from the concept that (a | b) & (!a | !b)  = (ab+a+b)(ab+1) and that xoring these two clauses will give us the count of the number of clauses that are true
 */
function clauseXorEqualsTheirCount(clauses){
    clauses = optimize(clauses)
    const count = {}
    const add = (key)=>{
        if(!count[key]) count[key]=0
        count[key]++
    }
    for (let clause of clauses) {
        const potentialRemovals=[]

        for (let variable of clause) {
            if(!variableValue(variable)){
                potentialRemovals.push(variable)
            }
        }
        add(clause.map(v=>clean(v)).sort().join(' '))
        // For all permutation of potentialRemovals add the clause without the variable(s)
        if(potentialRemovals.length===0) continue;
        for (let permutation of makePermutation(potentialRemovals)) {
            let newClause = clause
            for(let v of permutation){
                newClause = removeVariable(newClause,v)
            }
            if(newClause.length===0){
                add("F")
            } else{
                add(newClause.map(v=>clean(v)).sort().join(' '))
            }
        }


    }
    // Remove all that are even
    for (let key in count) {
        if(count[key]%2===0){
            delete count[key]
        }
    }
    console.log(count)

    // convert count to clauses
}

function splitAndFlip(clauses){
    const v = clauses[0][0]
    console.log(clauses.map(clause => removeVariable(clause, v)));
}
function mirror(clauses){
    // Get all variables
    const variables = clauses.reduce((acc,clause)=>{
        clause.forEach(v=>{
            if(!acc.includes(clean(v))) acc.push(clean(v))
        })
        return acc
    },[])
    // generate clauses mirror where variable v becomes variables[variables.length - variables.indexOf(v) -1]
    const mirrorClauses = clauses.map(clause=>{
        return clause.map(v=>{
            return sign(v)+variables[variables.length - variables.indexOf(clean(v)) -1]
        })
    })

    // find a xor of clauses and mirrorClauses
    const uniqueClauses = mirrorClauses.filter(clause=>{
        // console.log(clauses.find(c=>sameClause(c,clause))) //1 2 3 0
        return !clauses.find(c=>sameClause(c,clause))
    })

    console.log(mirrorClauses)
    console.log(uniqueClauses);
    console.log(clauses)
}

function folding(clauses){
    console.log(getClausesAssuming(clauses, '-1'));
}


function getClausesAssuming(clauses,assumption){
    return clauses.filter(clause=>{
        return clause.find(v=>similar(v,assumption))
    }).map(clause=>{
        const found = clause.find(v=>similar(v,assumption))
        if(found){
            return clause.filter(v=>v!==found).map(x=>x+'')
        }
        return clause
    })
}

function bloomFilter(clauses){
    const bloom={}
    // populate with 0
    for (let clause of clauses) {
        clause.forEach(v=> {
            if(!bloom[clean(v)]) {
                bloom[clean(v)] = 0
                bloom['-'+clean(v)] = 0
            }
        })
    }
    /*

    -1 2 3 0
-2 1 3 0
-3 1 2 0
-3 -2 -1 0
     */
    // count 1 2 -3
    console.log(clauses)
    const keys=Object.keys(bloom)
    for (let clause of clauses) {
        const sameAsClause = Math.pow(2, keys.length/2 - 1);
        let differentFromClause = 0
        differentFromClause = Math.pow(2, keys.length/2 - 1)-Math.pow(2, keys.length/2 - clause.length );
        // const notInClause = (Math.pow(2,keys.length/2) - Math.pow(2,clause.length -1)) / 2;
        for (let key of keys) {
            let x = false;
            // if((key)==='1')x=true
           if(clause.find(v=>clean(v)===clean(key)) !== undefined){
               if(clause.find(v=>(v)===(key))){
                   // if(x) console.log('sameAsClause',sameAsClause)

                   bloom[key]+=sameAsClause
               } else {
                   // if(x) console.log('differentFromClause',differentFromClause)

                   bloom[key]+=differentFromClause
               }
           } else {
               // if(x) console.log('notInClause',differentFromClause)

               bloom[key]+= differentFromClause;
           }
        }
    }
    for (let i = 0; i < keys.length/2; i++) {
        const trueKey = clean(keys[i])
        const falseKey = not(trueKey)
        console.log(bloom[trueKey],bloom[falseKey])
        // bloom[trueKey] = bloom[trueKey]===bloom[falseKey] ? 'x': bloom[trueKey]>bloom[falseKey] ? '1':'0'
        // delete bloom[falseKey]
    }
    console.log(bloom)

}

function getVarCount(clauses, shouldClean=true){
    const count = {}
    if(shouldClean){
        for (let clause of clauses) {
            for (let variable of clause) {
                if(!count[clean(variable)]) count[clean(variable)]=0
                count[clean(variable)]++
            }
        }
    }
    else {
        for (let clause of clauses) {
            for (let variable of clause) {
                if(!count[variable]) count[variable]=0
                count[variable]++
            }
        }
    }
    return count
}
function similar(v1,v2){
    return v1.toString()===v2.toString()
}

function sameClause(clause1,clause2){
    return (clause1.sort().join(' ')===clause2.sort().join(' '))
}
function not(v){
    if(v.startsWith('-')) return v.substr(1)
    else return '-'+v;
}
function isNeg(literal) {
    return literal.startsWith('-');
}

function sign(v){
    if(v.startsWith('-')) return '-'
    else return '';
}
function variableValue(v){
    return !v.startsWith('-')
}


function clean(v){
    return v.replace('-','')
}

function removeVariable(clause,variable){
    return clause.filter(v=>clean(v)!==clean(variable))
}

function containsVariable(clause,variable){
    return clause.find(v=>clean(v)===clean(variable))!==undefined
}

function containsVariableWithSign(clause, variable){
    return clause.find(v=>v===variable) !== undefined
}

function setVariable(clauses,variable, value){
    // console.log('setting',variable,value)
    // console.log('setting',variable,value)
    const newClauses = []
    clauses.forEach(clause=>{
        if(!containsVariable(clause,variable)){
            newClauses.push(clause)
            return
        }
        const vValue = variableValue(clause.find(v=>clean(v)===clean(variable)))
        if(vValue!==value){
            if(clause.length===1){
                // console.log(clauses, variable, value,vValue,clause)
                console.log('u')
                throw new Error('Unsatisfiable')
            }
            newClauses.push(removeVariable(clause,variable))
        }
    })
    return newClauses;
}

function replaceVariable(clauses,variable, replacement, flip){
    // replace a variable with another variable, and optionally flip it
    const newClauses = []
    clauses.forEach(clause=>{
        if(!containsVariable(clause,variable)){
            newClauses.push(clause)
            return
        }

        const newClause = clause.map(v=>{
            if(clean(v)===clean(variable)){
                const replaced = sign(v)+clean(replacement)
                return flip ? not(replaced) : replaced
            }
            return v
        })
        // check for [-a ... a]
        if(newClause.find(v=>v===replacement) && newClause.find(v=>v===not(replacement))){
            return
        }
        // remove duplicates
        newClauses.push(newClause.filter((v,i)=>newClause.indexOf(v)===i))
    })

    return newClauses;

}

function optimize(clauses){
    let dirty= true;
    while(dirty){
        console.log(clauses.length)
        dirty = false
        let simpleVars = {} // vars that are only true or only false
        let notSimpleVars = {} // vars that are both true and false
        for (let clause of clauses) {
            // if a clause is only one variable, set it
            if(clause.length===1){
                clauses = setVariable(clauses.filter(c=>c!==clause),clause[0],variableValue(clause[0]))
                dirty = true
                break
            }
            // Go through all variables and check if they are only true or only false
            for (let variable of clause) {
                if(!simpleVars[clean(variable)] && !notSimpleVars[clean(variable)]) simpleVars[clean(variable)] = variable
                if(simpleVars[clean(variable)]!==variableValue(variable)){
                    notSimpleVars[clean(variable)] = variable
                    delete simpleVars[clean(variable)]
                }
            }
        }

        if(Object.keys(simpleVars).length>0){
            for (let variable in simpleVars) {
                clauses = setVariable(clauses,variable,variableValue(simpleVars[variable]))
            }
            dirty = true
        }
        if(dirty) continue
        const cleanedClauses = removeRedundantClauses(clauses)
        if(cleanedClauses.length!==clauses.length){
            dirty = true
            clauses = cleanedClauses
            // find any empty clauses

            continue;
        }
        const twoVarOptimizedClauses = optimizeTwoVariableCases(clauses)
        if(twoVarOptimizedClauses.length!==clauses.length){
            dirty = true
            clauses = twoVarOptimizedClauses
            continue;
        }

    }
    // remove duplicates
    return Object.keys(clauses.reduce((acc,clause)=>{
        acc[clause.sort().join(' ')]=clause
        return acc
    },{})).map(x=>x.split(' '))
}

function optimizeTwoVariableCases(clauses) {
    // Step 1: Collect all variables and their literals
    const variables = new Set();
    clauses.forEach(clause => {
        if (clause.length === 2) {
            clause.forEach(lit => {
                variables.add(clean(lit));
            });
        }
    });

    // Mapping from variable to index
    let index = 0;
    const varToIndex = {};
    const indexToVar = {};
    variables.forEach(variable => {
        varToIndex[variable] = index++;
        indexToVar[index - 1] = variable;
    });
    const numVars = variables.size;

    // Step 2: Build the implication graph
    const graph = [];
    for (let i = 0; i < 2 * numVars; i++) {
        graph.push([]);
    }

    // Helper functions
    function varIndex(varName, isNeg) {
        // Returns index in the graph for variable or its negation
        return varToIndex[varName] * 2 + (isNeg ? 1 : 0);
    }

    function addImplication(fromVar, fromNeg, toVar, toNeg) {
        const fromIdx = varIndex(fromVar, fromNeg);
        const toIdx = varIndex(toVar, toNeg);
        graph[fromIdx].push(toIdx);
    }

    // Step 3: Add implications based on clauses
    clauses.forEach(clause => {
        if (clause.length === 2) {
            const [litA, litB] = clause;
            const aVar = clean(litA);
            const bVar = clean(litB);
            const aNeg = isNeg(litA);
            const bNeg = isNeg(litB);

            // For clause (a ∨ b), add implications: ¬a ⇒ b and ¬b ⇒ a
            addImplication(aVar, !aNeg, bVar, bNeg);
            addImplication(bVar, !bNeg, aVar, aNeg);
        }
    });

    // Step 4: Find SCCs using Tarjan's Algorithm
    const indexMap = {};
    const lowLink = {};
    const indexCounter = { value: 0 };
    const onStack = {};
    const stack = [];
    const sccs = [];
    const sccMap = {};

    function strongConnect(v) {
        indexMap[v] = indexCounter.value;
        lowLink[v] = indexCounter.value;
        indexCounter.value++;
        stack.push(v);
        onStack[v] = true;

        graph[v].forEach(w => {
            if (indexMap[w] === undefined) {
                strongConnect(w);
                lowLink[v] = Math.min(lowLink[v], lowLink[w]);
            } else if (onStack[w]) {
                lowLink[v] = Math.min(lowLink[v], indexMap[w]);
            }
        });

        if (lowLink[v] === indexMap[v]) {
            const scc = [];
            let w;
            do {
                w = stack.pop();
                onStack[w] = false;
                scc.push(w);
                sccMap[w] = sccs.length;
            } while (w !== v);
            sccs.push(scc);
        }
    }

    for (let v = 0; v < graph.length; v++) {
        if (indexMap[v] === undefined) {
            strongConnect(v);
        }
    }

    // Step 5: Check for unsatisfiability
    for (let i = 0; i < numVars; i++) {
        const varIdx = i * 2;
        const negVarIdx = varIdx + 1;
        if (sccMap[varIdx] === sccMap[negVarIdx]) {
            console.log('Unsatisfiable due to variable:', indexToVar[i]);
           throw 'Unsatisfiable'
        }
    }

    // Step 6: Assign variables based on SCCs
    const assignment = {};
    const sccValues = {};
    // Process SCCs in reverse topological order
    const sccOrder = sccs.slice().reverse();

    sccOrder.forEach(scc => {
        scc.forEach(node => {
            const varIdx = Math.floor(node / 2);
            const isNeg = node % 2 === 1;
            const varName = indexToVar[varIdx];
            if (assignment[varName] === undefined) {
                assignment[varName] = !isNeg;
            }
        });
    });

    // Step 7: Build variable equivalence classes
    const parent = {};
    function find(u) {
        if (parent[u] === undefined) {
            parent[u] = u;
        }
        if (parent[u] !== u) {
            parent[u] = find(parent[u]);
        }
        return parent[u];
    }

    function union(u, v) {
        const pu = find(u);
        const pv = find(v);
        if (pu !== pv) {
            parent[pu] = pv;
        }
    }

    // Variables in the same SCC are equivalent
    sccs.forEach(scc => {
        const varsInScc = new Set();
        scc.forEach(node => {
            const varIdx = Math.floor(node / 2);
            const isNeg = node % 2 === 1;
            const varName = indexToVar[varIdx];
            const lit = isNeg ? '-' + varName : varName;
            varsInScc.add(lit);
        });
        const varsArray = Array.from(varsInScc);
        for (let i = 1; i < varsArray.length; i++) {
            union(varsArray[0], varsArray[i]);
        }
    });

    // Step 8: Prepare replacements
    const replacements = {};
    Object.keys(parent).forEach(lit => {
        const root = find(lit);
        replacements[lit] = root;
    });

    // Step 9: Replace variables in clauses
    const newClauses = [];
    clauses.forEach(clause => {
        const newClause = clause.map(lit => {
            const litClean = isNeg(lit) ? '-' + clean(lit) : clean(lit);
            const replaced = replacements[litClean] || litClean;
            return replaced.startsWith('-') ? '-' + clean(replaced) : clean(replaced);
        });

        // Remove duplicates
        const uniqueClause = Array.from(new Set(newClause));
        // Remove tautologies
        const varsInClause = uniqueClause.map(clean);
        if (new Set(varsInClause).size !== uniqueClause.length) {
            // Clause is a tautology; skip it
            return;
        }
        newClauses.push(uniqueClause);
    });
    return newClauses;
}

function removeRedundantClauses(clauses) {
    const variableMap = new Map(); // key: sorted variables without signs

    // Build the variable map
    for (const clause of clauses) {
        const variables = clause.map(v => v.replace('-', '')).sort();
        const key = variables.join(' ');
        if (!variableMap.has(key)) {
            variableMap.set(key, []);
        }
        variableMap.get(key).push(clause);
    }

    const clausesToRemove = new Set();

    // For each group of clauses with the same variables
    for (const [key, group] of variableMap.entries()) {
        // Compare each pair in the group
        for (let i = 0; i < group.length; i++) {
            const clauseA = group[i];
            const mapA = {};
            for (const lit of clauseA) {
                const varName = lit.replace('-', '');
                mapA[varName] = lit;
            }
            for (let j = i + 1; j < group.length; j++) {
                const clauseB = group[j];
                const mapB = {};
                for (const lit of clauseB) {
                    const varName = lit.replace('-', '');
                    mapB[varName] = lit;
                }
                let differences = 0;
                let differingVar = null;
                for (const varName of Object.keys(mapA)) {
                    const litA = mapA[varName];
                    const litB = mapB[varName];
                    if (litA !== litB) {
                        if (litA === '-' + litB || '-' + litA === litB) {
                            differences++;
                            differingVar = varName;
                        } else {
                            differences = 2; // More than one difference or literals not complements
                            break;
                        }
                    }
                }
                if (differences === 1) {
                    // Clauses differ by exactly one literal which is complemented
                    const combined = clauseA.filter(v => v.replace('-', '') !== differingVar);
                    if (combined.length > 0) {
                        clausesToRemove.add(clauseA);
                        clausesToRemove.add(clauseB);
                        clauses.push(combined);
                    } else {
                        console.log('Empty clause detected, possibly unsatisfiable');
                    }
                }
            }
        }
    }

    return clauses.filter(c => !clausesToRemove.has(c));
}
// converts all clauses of the form (... | b)& (... | !b) to (...)
// function removeRedundantClausesz(clauses){
//     const newClauses = []
//     const clausesToRemove = []
//     outer: for (let clause1 of clauses) {
//         for(let clause2 of clauses){
//             if(clause1!==clause2){
//                // check that they have the same (cleaned) variables
//                 if(clause1.map(v=>clean(v)).sort().join(' ')===clause2.map(v=>clean(v)).sort().join(' ')){
//                     // check that there is exactly one variable that is different
//                     let diff = 0
//                     let diffVar;
//                     for (let variable of clause1) {
//                         if(!clause2.includes(variable)){
//                             diffVar = variable
//                             diff++
//                         }
//                     }
//                     if(diff===1){
//                        const combined = removeVariable(clause1,diffVar)
//                         if(combined.length>0){
//                             newClauses.push(combined)
//                             clausesToRemove.push(clause1,clause2)
//                         } else console.log('empty clause probably unsatisfiable')
//                         break outer;
//                     }
//                 }
//
//             }
//         }
//     }
//     return clauses.filter(c=>!clausesToRemove.includes(c)).concat(newClauses)
//
// }
function* makePermutation(arr) {
    const length = arr.length;
    // Loop through all possible combinations and sub-combinations
    for (let i = 0; i < (1 << length); i++) {
        const subset = [];
        // Check each bit in the binary representation of i
        for (let j = 0; j < length; j++) {
            if ((i & (1 << j)) !== 0) {
                subset.push(arr[j]);
            }
        }
        if(subset.length > 0) yield subset.join('');
    }
}

function saveToDimacs(clauses){
    fs.writeFileSync(__dirname+'/output.dimacs',clausesToDimacs(clauses))
}

main()
