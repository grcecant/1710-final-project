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
    team_manager: one Manager
}

------- DATA --------
abstract sig Data {
    owner: one Employee,
    read_access: set Employee,
    write_access: set Employee
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
    CEO.manager = none
    CEO.level = 7
    CEO.team = none
    -- CEO data access?

    // distinct ids 
    all e1, e2: Employee | e1.id != e2.id implies e1 != e2
}

run {
    wellformed_employees
} for 5 Employee, 5 Team, 5 Data