#lang forge

open "tree.frg"

---------- TEST PREDICATES ----------

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
        (e in Engineer or e in HR) implies e.manager = e.team.team_manager
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
    some d: Data, e: Employee | {
        all d2 : Data - d, e2: Employee - e | {
            (d2.read_access' = d2.read_access and d2.write_access' = d2.write_access)
            e2.data' = e2.data
        }
    }
}

pred change_team_permission_transition_choice {
    some d : Data, t : Team | {
        grantTeamReadAccess[d,t] or
        grantTeamWriteAccess[d,t]
    }
}

pred at_most_one_data_changed {
    some d: Data, t: Team {
        all d2 : Data - d, e: Employee - t.members | {
            (d2.read_access' = d2.read_access and d2.write_access' = d2.write_access)
            e.data' = e.data
        }
    }
}

pred access_control_hr_team_read {
    all d: EmployeeData, e: Employee | {
        e in d.read_access iff (e.team in HRTeam or e in d.owner)
        e.team in HRTeam implies e in d.read_access
        e in d.write_access iff (e in d.owner)
    }
}

pred access_control_owner_write_private {
    all d: PrivateData | d.read_access = d.owner and d.write_access = d.owner
}

pred access_control_company_data {
    all d: CompanyData, e: Employee| {
        // e can read d if they own it, OR if they are a manager (direct or indirect) of someone who owns it
        e in d.read_access iff (e in d.owner or e in d.owner.^manager)
        e in d.owner.^manager implies e in d.read_access
        // only direct manager has write access
        e = d.owner.manager implies e in d.write_access
        e in d.write_access iff (e in d.owner or e = d.owner.manager)
    }
}

pred access_control_no_more_than_2_files {
    all e: Employee | {
        let owned = {d: Data | e in d.owner} |
        (#owned <= 2 and #owned >= 0)
    }
}

pred access_control_transition_hr_team {
    some d: Data | {
        d in EmployeeData implies{
            all member : HRTeam.members{
                all d : Data{
                    member in d.read_access implies {
                        member in d.read_access'
                    }
                }
            }
        }
    }
}

pred access_control_transition_company_data_transfer {
    some d: Data | {
        d in CompanyData implies{
            some e: Employee | transferCompanyOwner[d,e]
        }
    }
}

pred access_control_private_data {
    some d: Data {
        d in PrivateData implies{
            all d: PrivateData, e: Employee {
                e not in d.owner' implies not (e in d.write_access')
            }
            some e : Employee | {
                grantReadAccess[d,e] or
                removeReadAccess[d,e]
            }
        }
    }
}

pred transfer_owner_test_pred[ d: Data, newOwner: Employee] {
    newOwner != d.owner

    let oldChain   = d.owner  + d.owner.^manager,
        newChain   = newOwner + newOwner.^manager,
        newWriters = newOwner + newOwner.manager | 
    {
        d.owner'        = newOwner
        d.read_access'  = (d.read_access  - oldChain) + newChain
        d.write_access' = (d.write_access - oldChain) + newWriters

        newOwner in d.read_access' and newOwner in d.write_access'
        all m: Employee | m in d.write_access' implies m in d.read_access'
    }
}


---------- PBT TEST SUITES ----------
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
}

test suite for changePermissionTransition {
    assert {(changePermissionIndividualTransition and not changePermissionTeamTransition) or
    (changePermissionTeamTransition and not changePermissionIndividualTransition)} is necessary for changePermissionTransition
}

test suite for accessControlStarting {
    assert access_control_hr_team_read is necessary for accessControlStarting
    assert access_control_owner_write_private is necessary for accessControlStarting
    assert access_control_company_data is necessary for accessControlStarting
    assert access_control_no_more_than_2_files is necessary for accessControlStarting
}

test suite for accessControlTransition {
    assert access_control_transition_hr_team is necessary for accessControlTransition
    assert access_control_transition_company_data_transfer is necessary for accessControlTransition
    assert access_control_private_data is necessary for accessControlTransition
}

test suite for transferCompanyOwner {
    assert all d: Data, e: Employee | transfer_owner_test_pred[d, e] is necessary for transferCompanyOwner[d, e]
}

test suite for accessControlTraces {
    assert initState is necessary for accessControlTraces
    assert accessControlStarting is necessary for accessControlTraces
    assert always wellformed_data is necessary for accessControlTraces
    assert always wellformed_files is necessary for accessControlTraces
    assert always validStateChange is necessary for accessControlTraces
    assert always accessControlTransition is necessary for accessControlTraces
    assert HRTeamSize is necessary for accessControlTraces
    assert some d: CompanyData, e: Employee | eventually transferCompanyOwner[d, e] is necessary for accessControlTraces
}

------------ COMBINED TESTING ------------

test expect {
    -- passes, but takes a long time
    individual_and_team_change_are_exclusive_guard: {
        randomTraces implies always {
            not (changePermissionIndividualTransition and changePermissionTeamTransition)
        }
    } is checked

    grant_then_remove_read: {
        accessControlTraces
        eventually {
            some d: Data, e: Employee | {
                grantReadAccess[d, e]
                next_state removeReadAccess[d, e]
            }
        }
    } is sat

    -- passes, but takes a long time
    only_one_permission_change_at_a_time: {
        randomTraces implies always {
            changePermissionTransition
        }
    } is checked

    revoke_implies_prior_grant: {
        accessControlTraces implies (some d: Data, e: Employee | 
            {removeReadAccess[d, e] or removeWriteAccess[d, e]} implies once (grantReadAccess[d, e] or grantWriteAccess[d, e]))
    } is checked

    two_company_ownership_changes: {
        accessControlTraces
        some disj d1, d2: CompanyData | eventually d1.owner != d1.owner' and eventually d2.owner != d2.owner'
    } is sat

    hr_grant_indiv_revoke_safe: {
        accessControlTraces
        eventually {
            some d: EmployeeData, t: Team | {
                all e: HRTeam.members | {
                    e in d.read_access
                    next_state
                    (some e2: Employee - HRTeam.members | {
                        grantReadAccess[d, e2]
                        next_state removeReadAccess[d, e2]
                    })
                }
            }
        }
    } is sat

    private_data_ownership_cannot_transfer: {
        accessControlTraces implies always {
            all d: PrivateData | d.owner = d.owner'
        }
    } is checked

    some_permission_change_each_state: {
        accessControlTraces implies always {
            some d: Data, e: Employee | (not e in d.read_access => e in d.read_access') or (not e in d.write_access => e in d.write_access')
        }
    } is checked

    hrNeverOwnsData: {
        accessControlTraces implies always {
            all d: Data | d.owner not in HRTeam.members
        }
    } is checked
}
