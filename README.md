# CS1710 Final Project: Role-Based Access Control of a Company

#### By Grace Cantarella, Yabeke Zike, and Josh Okwaning

### Our Model

Our model represents Role-Based Access Control (RBAC) of a company. RBAC is a system in which a user's role mediates their access to different permissions, in this case of different data. We aimed to create traces that, on a somewhat simplified level from a real company, showed how different types of data could transfer in ownership or read/write access over time. Through this, we were aiming to see whether we could expose some sort of vulnerability or possible exploit in a permissions-based structure such as this one.

There are three types of data in our system, which all extend an abstract Data sig — CompanyData, EmployeeData, and PrivateData. CompanyData represents any data which an employee may own that pertains to the company itself, such as an engineer's code file, a document with notes from a team's weekly standups, or a company's end of quarter earnings report. CompanyData is accessible by its owner, the owner's direct manager who has both write and read access, and all managers reachable through the direct manager (up until the CEO) who have read access. EmployeeData represents data which is specific to an employee, but not confidential, such as their W2, paystub, college transcript, and I-9. EmployeeData is accessible by the owner and all HR employees on the HRTeam, who have read access. PrivateData is data that is confidential and sensitive which pertains to a specific employee, such as their SSN or a private note written on their computer. Private data is only accessible by the owner to begin with. This is certainly a general abstraction of how data works in a real company, and each company likely has its own method of discerning what type of data warrants what type of access, or determining security implications of data. For example, see Brown's classification of level 1, 2, and 3 data [here](https://it.brown.edu/policies/data-risk-classifications). However, we believed this split into company, employee, and private data largely encompassed a generalization of how companies we've worked at thought about data and privacy.

We represent four different types of employees which all extend an abstract Employee sig: Manager, Engineer, HR, and one CEO. Each team has one team manager, who is the direct manager of all employees on that team, a set of Employees who are members, and one (or no) team above (though the only team with no team_above value is the CEO's team). A Manager's manager is the manager of the directly above team. HR employees are only on the one HRTeam. CEO extends Manager, and is the highest ranking employee in the entire hierarchy.

We used Temporal Forge in our model because it made the most sense in helping us achieve changes to permissions through time. We originally considered writing a State sig such as how we did in Lab 4, but ultimately decided against it as we decided we would need more than just three or four states. Fields that are variables and thus mutable over time include an employee's set of Data, a Data's one owner, a Data's set of read access employees, and a Data's set of write access employees.

At the core of our model is the ability for a Data's access to change over time, depending on the type of data and the role of the employee. We developed our model in stages, and each stage proved more difficult and time-consuming than expected. We began by creating a simple structure of a company, but found that even this simple model required many intricate design choices—should the CEO have other members on their team? Should a team have multiple managers? How are we structuring the manager hierarchy? From here, we tacked on the idea of data ownership, which also led to discussions on how many owners a datum should have, who should have default read or write access, what type of data we wanted to represent, who decides permissions for a file, etc. We then began creating traces where ownership of files changed arbitrarily with changePermissionTransition, where either changePermissionIndividualTransition or changePermissionTeamTransition is called—essentially, in each state, one datum has at most one employee added to read or write access or removed from read or write access, or one datum has an entire team added to write or read access. Through these traces we wanted to ensure that our base model made sense and that we were able to generate longer traces where permissions changed through time, albeit somewhat arbitrarily. Lastly, we moved on to constraining changes in permission based on role and type of data. This proved to be the largest challenge for us.

<!-- (what the model proved) -->

### Scope, Tradeoffs, and Limitations

The scope of our model is limited by the sheer number of variables required for even a run with fewer than 10 Employees. We may be able to model smaller companies, perhaps early-stage startups, but not larger companies which could have hundreds of thousands of employees, like Google or Amazon. Our model is also limited to a few different sigs which extend Employee; it would be extremely unrealistic for us to model every type of employee which exists in a real company.

As mentioned earlier, we generalized Data into CompanyData, EmployeeData, and PrivateData. In our ideal world we would've abstracted further to create specific sigs like W2, SSN, GoogleDoc, JavaFile, ExpenseReport, PostItNote, etc. but this was not realistic based on Forge's limitations and the thousands of types of files that really exist in a company.

Another tradeoff was our representation of the team structure as directly linear. It of course makes sense that, tracing up the chain, each team inherently reports to the CEO as the highest "power," but most companies do not employ a strictly linear hierarchy structure of every team. At least at the companies we have worked at, different engineering teams were not above or below one another, especially cross-functionally. Similarly to how we had to generalize for Data and Employee, we also had to generalize for Team here to create a model that was readable and traceable, that connected back to the CEO at the top of the chain.

In terms of limitations, our model cannot represent companies that employ multiple managers per team or have equilevel teams. We do not support custom chains of delegation, which adds some aspect of rigidity; for example, if HR needed immediate emergency access to someone's private data, this is not necessarily possible.

In addition, there was a large number of different permissions designs we could've chosen from in structuring our model, such as the Bell-LaPadula model (write-up, read-down). For CompanyData, we decided upon an employee's direct manager having write and read access and all reachable managers having read access for the following reasons: 
1) Enables direct oversight from an employee's higherup, but not abuse of power in write access by even more senior employees (like the CEO).

2) Lends greater control to the owner, who is able to share write access with whomever they desire.

3) Data can never be left uneditable, as there is always one owner and one person with write access.

<!-- (explain goals) -->

### Goals

TBD

### Visualization

We relied exclusively on Cope and Drag and Sterling's built-in visualization for this project, and did not create a custom visualization. We found that the natural structure of directed arrows representing fields pointing to specific nodes made a lot of sense for this access control structure. We created a custom Cope and Drag file (included in this repo) to help mimic the linear hierarchical structure of the company we intended to model.

<!-- INSERT IMAGES OF INSTANCES !!!!!!!!!!!!!!!!!!!!! -->
##### Sterling Visualization: 
![Screenshot of Sterling Visualization](/images/sterling.png)

#### CND Visualization:
![Screenshot of CND Visualization](/images/cnd.png)

The three orientation constraints we introduced in the CND file were that 1) the teams should be arranged in a linear structure, where the team at the end of the chain should be at the bottom, and from there all team_above teams are arranged towards the top, ending with the CEO's team which is always the highest team; 2) members should be arranged next to the team in which they work, from left to right; 3) an employees's data should be arranged directly below them to indicate ownership. In Cope and Drag, we also often entered additional constraints on grouping to separate on, for example, data ownership or employee type. These constraints are not included in the submitted CND file as they were moreso used in our manual testing and verification as opposed to properties we wanted to highlight.

We did run into some issues with Cope and Drag; as the model got more convoluted with more and more sigs, we would get errors from Cope and Drag saying that certain edges would need to be unsticked, or other errors regarding impossible layouts ("You may have to click and drag these nodes slightly nodes to un-stick layout."). In these cases, we had to focus on the Sterling visualization which was more difficult to parse out manually, so instead we relied on reading the table form of data whenever this happened. It was especially bothersome as it would sometimes occur only in some states of the trace, and not all (we spent most of our time testing with tracelength 12).

### Testing

We employed thorough property-based testing for each predicate in our main tree.frg file. Because we used Temporal Forge, we decided against using examples as we remembered we were encouraged against it during the temporal forge assignment, and instead focused on testing properties that should hold between time states rather than trying to find specific instances of what Forge might model (which, in a model like this, are exceedingly complicated and numerous). We also included test-expect blocks that tested mutual exclusion for different preds that should not fire at the same time, and testing certain sequences of predicates based off of intended performance. As mentioned above, much of our testing also took place through manual verification of Sterling and Cope and Drag trace visualizations. 

### Collaboration

Collaborators: N/A
