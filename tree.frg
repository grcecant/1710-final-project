#lang forge/temporal

option max_tracelength 12
option min_tracelength 12

--- EMPLOYEES ----
abstract sig Employee {
    manager: lone Employee,
    team: lone Team,
    var data: set Data
}

sig Manager extends Employee {}
one sig CEO extends Manager {}
sig Engineer extends Employee {}
sig HR extends Employee {}

------- TEAM / DEPARTMENT ------
sig Team {
    members: set Employee,
    team_manager: one Manager,
    team_above: lone Team
}

one sig HRTeam extends Team {}

------- DATA --------
abstract sig Data {
    var owner: one Employee,
    var read_access: set Employee,
    var write_access: set Employee
}

sig EmployeeData extends Data {}
sig CompanyData extends Data {}
sig PrivateData extends Data {}

--------------------------- PREDICATES -------------------------

--------- WELLFORMEDNESS ---------

pred wellformed_employees {
    no CEO.manager
}

pred wellformed_teams {
    // every team has one manager 
    all t: Team {
        t != CEO.team implies {one m: Manager | m in t.members and m = t.team_manager}
        t = CEO.team implies {one m: Manager | m in t.members and m = CEO}
    }

    // every manager is only the manager of one team 
    all m: Manager {
        one t: Team | m = t.team_manager and m in t.members
    }

    // every employee is on exactly one team 
    all e: Employee {
        all t: Team | {
            e in t.members implies e.team = t
            e.team = t implies e in t.members
        }
        one t: Team | t = e.team
    }

    // HR employees are in the HR team only
    all e: Employee | {
        e in HR implies e.team = HRTeam
        e.team = HRTeam implies (e in HR or e in Manager)
    }


    // Making it so that the hr team is points to the ceo team as thier team above
    // but is not included in the rest of the team hiearchy chain
    all hrt : HRTeam {
        hrt.team_above = CEO.team

        all t: Team | {
            hrt not in t.^team_above
        }
    }

    // every team has a team above it (except the first team), which is linear. CEO is the top of the team hierarchy
    all t: Team {
        t = CEO.team implies no t.team_above

        // The top team is reached by all other teams 
        t = CEO.team implies {
            all t2: Team - t |{
                t2 != HRTeam implies {
                    t in t2.^team_above
                }
            }
        }

        // All teams have some team above them
        all t2: Team - CEO.team | some t2.team_above
    }

    // team structure is linear hierarchical
    all t: Team - HRTeam {
        no t2: Team - HRTeam - t | t.team_above = t2.team_above
    }

    // there should only be one team with no team above (head of the chain). This team should be reachable from all other teams.
    #{t: Team | no t.team_above} = 1


    CEO.team.members = {CEO}
    CEO.team not in HRTeam

    // an employee's manager is the manager of their team
    // a manager's manager is the manager of the team_above
    all e: Employee {
        (e in Engineer or e in HR) implies e.manager = e.team.team_manager
        (e in Manager) implies e.manager = e.team.team_above.team_manager
    }
}

pred wellformed_files {
    // every data file has one owner
    all d: Data {
        one e: Employee | {
            d in e.data
            e in d.owner
        }
    }

    all d : Data {
        d.owner in d.read_access
        d.owner in d.write_access
    }
    
    all e: Employee, d: Data {
        // every employee has access to their own data
        d in e.data implies e in d.read_access and e in d.write_access and e in d.owner
    }

    // All hr employees (including manager) are owners of no data ***
    all hr: HRTeam.members|{
        no d : Data |{
            hr in d.owner
        }
    }
}

---------- DEFINING ACCESS CONTROL ----------
pred grantReadAccess[data: Data, grantAccess: Employee] {
    // // owner is not the one being granted access
    grantAccess != data.owner

    data.write_access' = data.write_access 
    data.read_access' = data.read_access + grantAccess
}

pred grantWriteAccess[data: Data, grantAccess: Employee]{
    // owner is not the one being granted access
    grantAccess != data.owner

    data.read_access' = data.read_access
    data.write_access' = data.write_access + grantAccess
}

pred removeReadAccess[data: Data, grantAccess: Employee]{
    // owner cannot have their access removed
    grantAccess != data.owner
    data.read_access' = data.read_access - grantAccess
    data.write_access' = data.write_access
}

pred removeWriteAccess[data: Data, grantAccess: Employee]{
    // // owner cannot have their access removed
    grantAccess != data.owner
    data.write_access' = data.write_access - grantAccess
    data.read_access' = data.read_access
}

pred grantTeamReadAccess[data: Data, team: Team]{
    // for all members in a team, grant them read access 
    data.read_access' = data.read_access + team.members
    data.write_access' = data.write_access 
}

pred grantTeamWriteAccess[data: Data, team: Team]{
    // for all members in a team, grant them write access
    data.write_access' = data.write_access + team.members
    data.read_access' = data.read_access
}

------------------ TRANSITIONS -----------------

// NOTE: probably need to change this for ownership changing preds as the owner won't be the same in both states
pred validStateChange {
    all e : Employee {
        all d : Data {
            d in CompanyData implies{
                e in d.owner implies {
                    d in e.data' 
                    e in d.write_access'
                    e in d.read_access'
                }
            } else{
                e in d.owner implies {
                    d in e.data' 
                    e in d.write_access'
                    e in d.read_access'
                    e in d.owner'
                }
            }
        }
    }
}

pred changePermissionIndividualTransition {
    some d : Data, e : Employee | {
        grantReadAccess[d,e] or
        grantWriteAccess[d,e] or
        removeReadAccess[d,e] or 
        removeWriteAccess[d,e]
    } 

    // at most one employee has their permissions changed
    let changed = {e: Employee |
        some d: Data |
            (e in d.read_access') and not (e in d.read_access) or
            not (e in d.read_access') and (e in d.read_access)
    } |
    #changed <= 1
}

pred changePermissionTeamTransition {
    some d : Data, t : Team | {
        grantTeamReadAccess[d,t] or
        grantTeamWriteAccess[d,t]
    }

    // at most one data has its permissions changed
    let changed = {d: Data | 
        d.read_access' != d.read_access or
        d.write_access' != d.write_access
    } |
    #changed <= 1

    // at most one team has its permissions changed -- people not on the team should not have any permissions changed
    let changedEmployees = { e: Employee |
        some d: Data |
            e in d.read_access' iff e not in d.read_access or
            e in d.write_access' iff e not in d.write_access
        } |
    {some t: Team |
        changedEmployees = t.members and
        {all t2: Team - t | no (changedEmployees & t2.members) }  
    }    
}

pred changePermissionTransition {
    // exclusive or: only one should be true at a time
    // either a team or an individual can be granted access
    (changePermissionIndividualTransition and not changePermissionTeamTransition) or
    (changePermissionTeamTransition and not changePermissionIndividualTransition)
}

pred accessControlStarting {
    // HRTeam members can read all EmployeeData
    all d: EmployeeData, e: Employee | {
        e in d.read_access iff e.team in HRTeam
        e.team in HRTeam implies e in d.read_access
    }
    
    // only the owner can read or write PrivateData
    all d: PrivateData | d.read_access = d.owner and d.write_access = d.owner
    
    // company data
    all d: CompanyData, e: Employee| {
        // e can read d if they own it, OR if they are a manager (direct or indirect) of someone who owns it
        e in d.read_access iff (e in d.owner or e in d.owner.^manager)
        e in d.owner.^manager implies e in d.read_access
        // only direct manager has write access
        e = d.owner.manager implies e in d.write_access
    }

    // no person should own more than 2 files for readability purposes in the visualizer
    all e: Employee | {
        let owned = {d: Data | e in d.owner} |
        #owned <= 2
    }
}

/*
Only one persons permissions or teams permissions should change at each state
hr team: employee data privileges should never change
pass in a type of data, and if it is that type of data, then execute that specifically
*/
pred accessControlTransition{
    // at most one employee permissions changed already enforcded in changePermissionIndividualTransition 

    // hr team access should not change between states

    some d: Data |{
        d in EmployeeData implies{
            all member : HRTeam.members{
                all d : Data{
                    member in d.read_access implies {
                        member in d.read_access'
                    }
                }
            }
        }

        // // if a person no longer is the owner of thee document, initially they should not be able to both read and write
        d in PrivateData implies{
            all d: PrivateData, e: Employee {
                e not in d.owner' implies not (e in d.write_access')
            }
            some e : Employee | {
                grantReadAccess[d,e] or
                removeReadAccess[d,e]
            }
        }

        // in the case that the person in the next state is no longer the owner (company data), it means that 
        // that the propagation of managers also having access does not hold and should be changed
        // as we percolate up from manager to manager
        d in CompanyData implies{
            transferCompanyOwner
        }

       all d2 : Data - d | (d2.read_access' = d2.read_access and d2.write_access' = d2.write_access)
    }
}

pred transferCompanyOwner{
    /* 
    Transfer Company Data Rules:
        - At some state we would want owner ship of the document to change
        so that logic for companyData in accessControlTransition can execute
    */
    some d: CompanyData {
        let newOwners = { e : Employee | e != d.owner} |
        some e: newOwners | {
                // firstly, make sure that read and write access of the former employee is gone
                // removeReadAccess[d, d.owner]
                // removeWriteAccess[d, d.owner]

                d.owner not in d.read_access'
                d.owner not in d.write_access'

                // Remove read and write access for all managers of the former owner
                all m: Employee |
                    m in d.owner.^manager => {
                        m not in d.read_access'
                        m not in d.write_access'
                        // removeReadAccess[d, m]
                        // removeWriteAccess[d, m]
                    }
                d.owner' != d.owner
                d.owner' = e
                e in d.read_access'
                e in d.write_access'
                // grant access for new employee
                all m: Employee |
                    m in e.manager => {
                        m in d.read_access'
                        m in d.write_access'
                        // grantReadAccess[d,m] 
                        // grantWriteAccess[d,m]
                    } and
                    m in e.manager.^manager => {
                        e in d.read_access'
                        // grantReadAccess[d,m]  
                    }
                    and
                    (m not in e.manager and m not in e.manager.^manager) =>{
                        m not in d.read_access'
                        m not in d.write_access'
                    }

        }
    }
}

pred initState {
    wellformed_employees
    wellformed_teams
    wellformed_files
}

pred randomTraces {
    initState
    accessControlStarting
    always {validStateChange}
    always {changePermissionTransition}
}

pred traces {
    initState
    accessControlStarting
    always {validStateChange}
    always {accessControlTransition}
    // eventually {transferCompanyOwner}
}

sevenEmployee: run {
    traces
} for exactly 7 Employee, exactly 3 Team, exactly 2 PrivateData, exactly 2 EmployeeData, exactly 2 CompanyData


companyData: run {
    traces
} for exactly 10 Employee, exactly 4 Team, exactly 2 PrivateData, exactly 4 CompanyData

// NOTE: add more run functions for original transition traces 

------------ SECURITY -------------

pred onlyAllowedMayRead {
  all d : Data, e : Employee |
    let permitted =
        (e in d.owner) or
        (d in EmployeeData and e in HRTeam.members) or
        (d in CompanyData and (e in d.owner.^manager)) or
        (d in PrivateData and e in d.owner)
    |
    e in d.read_access implies permitted
}

-- Question 1: Are any employees able to access (read-only) data that has not been explicitly shared with them in the starting state?
-- UNSAT: which shows us that there is no counterexample, verifying this security aspect
onlyAllowedReadAccess: check {traces implies onlyAllowedMayRead }


pred privateDataNoFullAccessForNonOwner {
  all d : PrivateData, e : Employee |
    e not in d.owner implies
      not (e in d.read_access and e in d.write_access)
}

-- Question 2: Are any employees able to read and write private data that they do not own, in any state?
-- UNSAT: which shows us that there is no counterexample, verifying this security aspect
privateDataNoFullAccess: check { traces implies always { privateDataNoFullAccessForNonOwner }}


pred privateDataOwnerKeepsSomeAccess {
  all d : PrivateData |
    d.owner in d.read_access + d.write_access
}

-- Question 3: Does the owner of private data always have some access to it, in any state?
-- UNSAT: which shows us that there is no counterexample, verifying this security aspect
privateDataOwnerAccess: check { traces implies always { privateDataOwnerKeepsSomeAccess }}


pred employeeDataHRRead {
  all hr : HRTeam.members, d : EmployeeData |
    hr in d.read_access
}

-- Question 4: Are all HR employees able to read all employee data, in any state?
-- UNSAT: which shows us that there is no counterexample, verifying this security aspect
hrReadImmutable: check { traces implies always { employeeDataHRRead } }

pred singleFileAccessChange {
  let changed = { d : Data |
        d.read_access' != d.read_access or
        d.write_access' != d.write_access } |
  #changed <= 1
}

-- Question 5: Is it possible for more than one file to have its access changed in a single state transition?
-- UNSAT: which shows us that there is no counterexample, verifying this security aspect
singleFileChangeCheck: check { traces implies always { singleFileAccessChange } }

