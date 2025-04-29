#lang forge


--- EMPLOYEES ----
abstract sig Employee {
    manager: lone Employee,
    // level: one Int,
    team: lone Team,
    data: set Data
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
    owner: one Employee,
    read_access: set Employee,
    write_access: set Employee
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
        all t: Team | e in t.members implies e.team = t
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
    // every data file has ONE owner
    all d: Data {
        one e: Employee | d.owner = e
        d.owner in d.read_access and d.owner in d.write_access
        // write access encompasses read access
        d.read_access in d.write_access
    }

    all e: Employee {
        // every employee has access to their own data
        all d: Data | d in e.data implies e in d.read_access or e in d.write_access
    }
}

pred init {
    wellformed_employees
    wellformed_teams
    wellformed_files
}

threeTeam: run {
    init
} for 5 Employee, exactly 3 Team, 5 Data