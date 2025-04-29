#lang forge


--- EMPLOYEES ----
abstract sig Employee {
    id: one Int,
    manager: lone Employee,
    level: one Int,
    team: lone Team,
    data: set Data
}

one sig CEO extends Employee {}
sig Manager extends Employee {}
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
    owner: one Employee,
    read_access: set Employee,
    write_access: set Employee,
    file_type: one Filetype
}

sig EmployeeData extends Data {}
sig CompanyData extends Data {}
sig PrivateData extends Data {}

abstract sig Filetype {}
sig WorkDocument extends Filetype {}
sig W2 extends Filetype {}
sig SSN extends Filetype {}

------ PREDICATES ------
pred wellformed_employees {
    no CEO.manager
    CEO.level = 7
    -- CEO data access?

    // distinct ids 
    all e1, e2: Employee | e1.id != e2.id implies e1 != e2
}

pred wellformed_teams {
    // every team has one manager
    all t: Team | one m: Manager | t.team_manager = m

    // every team has at least one employee
    all t: Team | some e: Employee | e in t.members

    all t: Team | {
        t != CEO.team implies {
            some t_above: Team | {
                t.team_above = t_above
                t.team_above != t
            }
        } 
    }

    // every employee is on a team, except the CEO
    // CEO.team = none
    all e: Employee | e != CEO implies (some e.team and e.team in Team)

    // every employee has a manager, except the CEO, and their manager is the team's manager
    // NOTE: this is not working right now because the team manager becomes their own manager
    all e: Employee | {
        e = Manager implies {
            e.manager = e.team.team_above.team_manager
        } else {
            e != CEO implies {
                e.manager = e.team.team_manager
            }
        }
    } 
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
    // check if the owner passed in is actually the owner of the data
    data'.file_type = data.file_type // the filetype should not change
    data'.write_access = data.write_access 
    // in the case that the owner is the one that is passed
    data'.read_access = data.read_access + grantAccess
}

pred grantWriteAccess[data: Data, grantAccess: Employee]{
    data'.file_type = data.file_type
    data'.read_access = data.read_access
    // in the case that the owner is the one that is passed
    data'.read_access = data.read_access + grantAccess
}

pred init {
    wellformed_employees
    wellformed_teams
}

run {
    init
} for 5 Employee, 5 Team, 0 Data