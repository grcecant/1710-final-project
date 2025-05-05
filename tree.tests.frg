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
}

pred wellformed_file_access {
    all e: Employee, d: Data {
        // every employee has access to their own data
        d in e.data implies e in d.read_access and e in d.write_access
    }
}

pred grant_read_access_test_pred[data: Data, grantAccess: Employee] {
    grantAccess != data.owner

    data.write_access' = data.write_access 
    data.read_access' = data.read_access + grantAccess
}

pred grant_write_access_test_pred[data: Data, grantAccess: Employee] {
    grantAccess != data.owner

    data.write_access' = data.write_access + grantAccess
    data.read_access' = data.read_access
}

pred remove_read_access_test_pred[data: Data, grantAccess: Employee] {
    grantAccess != data.owner
    
    data.read_access' = data.read_access - grantAccess
    data.write_access' = data.write_access
}

pred remove_write_access_test_pred[data: Data, grantAccess: Employee] {
    grantAccess != data.owner

    data.write_access' = data.write_access - grantAccess
    data.read_access' = data.read_access
}

pred change_permission_individual_transition_choice {
    some d : Data, e : Employee | {
        grantReadAccess[d,e] or
        grantWriteAccess[d,e] or
        removeReadAccess[d,e] or
        removeWriteAccess[d,e]
    } 
}

pred at_most_one_employee_data_changed {
    // at most one employee has their permissions changed
    let changed = {e: Employee |
        some d: Data |
            (e in d.read_access') and not (e in d.read_access) or
            not (e in d.read_access') and (e in d.read_access)
    } |
    #changed <= 1
}

pred change_team_permission_transition_choice {
    some d : Data, t : Team | {
        grantTeamReadAccess[d,t] or
        grantTeamWriteAccess[d,t]
    }
}

pred at_most_one_data_changed {
    // at most one data has its permissions changed
    let changed = {d: Data | 
        d.read_access' != d.read_access or
        d.write_access' != d.write_access
    } |
    #changed <= 1
}

pred at_most_one_team_changed {
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

test suite for initState {
    assert wellformed_employees is necessary for initState
    assert wellformed_teams is necessary for initState
    assert wellformed_files is necessary for initState
}

test suite for grantReadAccess {
    assert all d: Data, e: Employee | grant_read_access_test_pred[d, e] is necessary for grantReadAccess[d, e]
}

test suite for grantWriteAccess {
    assert all d: Data, e: Employee | grant_write_access_test_pred[d, e] is necessary for grantWriteAccess[d, e]
}

test suite for removeReadAccess {
    assert all d: Data, e: Employee | remove_read_access_test_pred[d, e] is necessary for removeReadAccess[d, e]
}

test suite for removeWriteAccess {
    assert all d: Data, e: Employee | remove_write_access_test_pred[d, e] is necessary for removeWriteAccess[d, e]
}

test suite for changePermissionIndividualTransition {
    assert change_permission_individual_transition_choice is necessary for changePermissionIndividualTransition
    assert at_most_one_employee_data_changed is necessary for changePermissionIndividualTransition
}

test suite for changePermissionTeamTransition {
    assert change_team_permission_transition_choice is necessary for changePermissionTeamTransition
    assert at_most_one_data_changed is necessary for changePermissionTeamTransition
    assert at_most_one_team_changed is necessary for changePermissionTeamTransition
}

test suite for changePermissionTransition {
    assert {(changePermissionIndividualTransition and not changePermissionTeamTransition) or
    (changePermissionTeamTransition and not changePermissionIndividualTransition)} is necessary for changePermissionTransition
}

test suite for traces {
    assert initState is necessary for traces
    assert always validStateChange is necessary for traces
}