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

pred ownerPermissions{
    // the case that a person is the owner of the document they should have full access to the data
    all data: Data{
        // the owner should exist in both read_access and write_access
        data.read_access + data.owner
        data.write_access + data.owner
    }
}



pred init {
    wellformed_employees
    wellformed_teams
}

run {
    init
} for 5 Employee, 5 Team, 0 Data