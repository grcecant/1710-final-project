#lang forge/temporal

option max_tracelength 12
option min_tracelength 12

--- EMPLOYEES ----
abstract sig Employee {
    manager: lone Employee,
    // level: one Int,
    team: lone Team,
    var data: set Data
}

sig Manager extends Employee {}
one sig CEO extends Manager {}
sig Engineer extends Employee {}
sig Administrator extends Employee {}

------- TEAM / DEPARTMENT ------
sig Team {
    members: set Employee,
    team_manager: one Manager,
    team_above: lone Team
}

------- DATA --------
abstract sig Data {
    var owner: set Employee,
    var read_access: set Employee,
    var write_access: set Employee
}

sig EmployeeData extends Data {}
sig CompanyData extends Data {}
sig PrivateData extends Data {}

sig WorkDocument extends CompanyData {}
sig W2 extends EmployeeData {}
sig SSN extends PrivateData {}

------ PREDICATES ------
pred wellformed_employees {
    no CEO.manager
    // CEO.level = 7
    -- CEO data access?
}

pred wellformed_teams {
    // every team has one manager, and every manager is only the manager of one team 
    all t: Team {
        t != CEO.team implies {one m: Manager | m in t.members and m = t.team_manager}
        t = CEO.team implies {one m: Manager | m in t.members and m = CEO}
    }
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

    // every team has a team above it (except the first team), which is linear. CEO is the top of the team hierarchy
    all t: Team {
        // there should only be one team with no team above (head of the chain). This team should be reachable from all other teams.
        #{t: Team | no t.team_above} = 1

        all t: Team {
            t = CEO.team implies no t.team_above
            no t.team_above implies {
                all t2: Team - t | t in t2.^team_above
            }
        }
    }

    CEO.team.members = {CEO}

    // an engineer's manager is the manager of their team
    // a manager's manager is the manager of the team_above
    all e: Employee {
        (e in Engineer or e in Administrator) implies e.manager = e.team.team_manager
        e in Manager implies e.manager = e.team.team_above.team_manager
    }
}

pred wellformed_files {
    // every data file has an owner (could be more than one)
    all d: Data {
        one e: Employee | {
            d in e.data
            e in d.owner
        }
    }

    all d : Data {
        d.owner in d.read_access
        d.owner in d.write_access
        #d.write_access = 1
        #d.read_access = 1
    }
    
    all e: Employee {
        // every employee has access to their own data
        all d: Data | {
            d in e.data implies e in d.read_access and e in d.write_access
        }
    }
}

pred validStateChange {
    all e : Employee {
        all d : Data {
            e in d.owner implies {
                d in e.data' 
                e in d.write_access'
                e in d.read_access'
                e in d.owner'
            }
        }
    }
}

pred initState{
    wellformed_employees
    wellformed_teams
    wellformed_files
}

/*
The owner can give write or read access, or transfer ownership
Multiple owners 
    - Same access and level 
    - Both can approve ownership and share
    - Cannot remove each other/ change permissions for each other 
At each state, a document should have an owner
Someone can remove themselves
    - There must be an owner of the data at all times 
Can give access to teams as a whole 
Include different states where the access to a document happens (lab 4 for ref)
    - In the initial state, only the owner has access to the document 
modeling data that should be able to be accessed by anyone of a certain level
*/
pred grantReadAccess[data: Data, grantAccess: Employee] {
    // // owner is not the one being granted access
    grantAccess != data.owner

    data.write_access' = data.write_access 
    data.read_access' = data.read_access + grantAccess
}

pred grantWriteAccess[data: Data, grantAccess: Employee]{
    // // owner is not the one being granted access
    grantAccess != data.owner

    data.read_access' = data.read_access
    data.write_access' = data.write_access + grantAccess
}

pred removeReadAccess[data: Data, grantAccess: Employee]{
    // // owner cannot have their access removed
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

pred grantTeamWriteAccess[data: Data, team: Team]{
    // for all members in a team, grant them write access
    data.write_access' = data.write_access + team.members
    data.read_access' = data.read_access
}

pred grantTeamReadAccess[data: Data, team: Team]{
    // for all members in a team, grant them read access 
    data.read_access' = data.read_access + team.members
    data.write_access' = data.write_access 
}

pred changePermissionIndividualTransition {
    some d : Data, e : Employee | {
        grantReadAccess[d,e] or
        grantWriteAccess[d,e] or
        removeReadAccess[d,e] or 
        removeWriteAccess[d,e]
    } 
}

pred changePermissionTeamTransition {
    some d : Data, t : Team | {
        grantTeamReadAccess[d,t] or
        grantTeamWriteAccess[d,t]
    }
}

pred changePermissionTransition {
    // exclusive or: only one should be true at a time
    // either a team or an individual can be granted access
    (changePermissionIndividualTransition and not changePermissionTeamTransition) or
    (changePermissionTeamTransition and not changePermissionIndividualTransition)
}

pred atMostOneDataChanged {
    let changed = {d: Data | 
        d.read_access' != d.read_access or
        d.write_access' != d.write_access
    } |
    #changed <= 1
}

pred traces{
    initState
    always {validStateChange}
    // always {changePermissionTransition}
    always {changePermissionIndividualTransition}
    always {atMostOneDataChanged}

    // just for now to see how it propogates
    eventually{
        all d : Data |{
            all e : Employee |{
                e in d.read_access
                e in d.write_access
            }  
        }
    }
}

run {
    traces
} for exactly 5 Employee, exactly 3 Team, exactly 5 Data