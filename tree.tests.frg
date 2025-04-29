#lang forge

open "tree.frg"

------ TEST PREDICATES ------

pred wellformed_employee_CEO {
    no CEO.manager
}

pred wellformed_team_one_team_manager {
    // every team has one manager, and every manager is only the manager of one team 
    all t: Team {
        t != CEO.team implies {one m: Manager | m in t.members and m = t.team_manager}
        t = CEO.team implies {one m: Manager | m in t.members and m = CEO}
    }
    all m: Manager {
        one t: Team | m = t.team_manager and m in t.members
    }
}

pred wellformed_team_exactly_one_team {
    // every employee is on exactly one team 
    all e: Employee {
        all t: Team | e in t.members implies e.team = t
        one t: Team | t = e.team
    }
}

pred wellformed_team_team_above {
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
}

pred wellformed_team_CEO_team {
    CEO.team.members = {CEO}
}

pred wellformed_team_manager_structure {
    // an engineer's manager is the manager of their team
    // a manager's manager is the manager of the team_above
    all e: Employee {
        (e in Engineer or e in Administrator) implies e.manager = e.team.team_manager
        e in Manager implies e.manager = e.team.team_above.team_manager
    }
}

pred wellformed_file_owner {
    // every data file has ONE owner
    all d: Data {
        one e: Employee | d.owner = e
        d.owner in d.read_access and d.owner in d.write_access
        // write access encompasses read access
        d.read_access in d.write_access
    }
}

pred wellformed_file_access {
    all e: Employee {
        // every employee has access to their own data
        all d: Data | d in e.data implies e in d.read_access or e in d.write_access
    }
}

------ TEST SUITES ------
test suite for wellformed_employees {
    assert wellformed_employee_CEO is necessary for wellformed_employees

}

test suite for wellformed_teams {
    assert wellformed_team_one_team_manager is necessary for wellformed_teams
    assert wellformed_team_exactly_one_team is necessary for wellformed_teams
    assert wellformed_team_team_above is necessary for wellformed_teams
    assert wellformed_team_CEO_team is necessary for wellformed_teams
    assert wellformed_team_manager_structure is necessary for wellformed_teams
}

test suite for wellformed_files {
    assert wellformed_file_owner is necessary for wellformed_files
    assert wellformed_file_access is necessary for wellformed_files
}

test suite for init {

}