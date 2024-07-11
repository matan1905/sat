fs = require('fs')

function main(){
    const file = fs.readFileSync(__dirname+'/'+process.argv[2]+'.dimacs').toString()
    let clauses = (file).split('\n').map(x=>x.split(/\s+/).sort((a,b)=>{
        return a.replace('-','').localeCompare(b.replace('-',''))
    }).slice(1))

    // clauses = reOrderByImpact(clauses)
    // console.log(clauseXorEqualsTheirCount(clauses))
    // console.log(clauses)
    // solveByAddingInformation(clauses);
    // console.log(optimize(clauses).map(c=>c.join(' ')).sort())
    // console.log(createClauseThatIsNotInClauses(clauses))
    // clauses = optimize(clauses)
    // console.log(VarOrVarNot(VarOrVarNot(clauses)));
    let i = 0
    while (clauses.length<50_000_000) {
        clauses = VarOrVarNot(clauses)
        // // clauses = removeRedundantClauses(clauses)
        clauses = optimize(clauses)
        i++;
        console.log(i,'/',25180,' - ',clauses.length)
        if(clauses.length===0) return console.log('SAT')
    }
    // console.log(clausesToDimacs(clauses.sort((a,b)=>{
    //     a.map(v=>Number(clean(v))).sort().join(' ').localeCompare(b.map(v=>Number(clean(v))).sort().join(' '))
    // })))

}


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

function optimize(clauses){
    let dirty= true;
    while(dirty){
        dirty = false
        let simpleVars = {} // vars that are only true or only false
        let notSimpleVars = {} // vars that are both true and false
        for (let clause of clauses) {
            if(clause.length===1){
                // console.log('optimizing',clauses,clause,variableValue(clause[0]))
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
            // console.log('cleaned',clauses)
        }
    }
    // remove duplicates
    return Object.keys(clauses.reduce((acc,clause)=>{
        acc[clause.sort().join(' ')]=clause
        return acc
    },{})).map(x=>x.split(' '))
}
function removeRedundantClauses(clauses) {
    const clauseMap = new Map();
    const clausesToRemove = new Set();

    for (const clause of clauses) {
        const key = clause.map(clean).sort().join(' ');
        if (!clauseMap.has(key)) {
            clauseMap.set(key, clause);
        } else {
            const existingClause = clauseMap.get(key);
            const diff = clause.filter(v => !existingClause.includes(v));
            if (diff.length === 1) {
                const combined = removeVariable(clause, diff[0]);
                if (combined.length > 0) {
                    clausesToRemove.add(clause);
                    clausesToRemove.add(existingClause);
                    clauses.push(combined);
                } else {
                    console.log('empty clause probably unsatisfiable');
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

main()