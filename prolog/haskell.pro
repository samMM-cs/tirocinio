% Define the possible sexes
sex(male).
sex(female).

% A person tells the truth if they are male.
% If they are female, we don't know if a single statement is true without context,
% but we know a male CANNOT lie.
can_truthfully_say(male, Statement) :- Statement = true.
can_truthfully_say(female, _). % Females can say true or false statements.

solve(P1Sex, P2Sex, ChildSex, ChildSaid) :-
  % 1. Assign sexes to everyone
  sex(P1Sex),
  sex(P2Sex),
  sex(ChildSex),
  sex(ChildSaid),

  % 2. Define the Child's statement logic
  % If child is male, what they said MUST be true.
  (ChildSex = male -> ChildSaid = male ; true),

  % 3. Parent 1's Statement: "The child said 'I am a boy.'"
  % This is a single statement (S1).
  P1SaysS1 = (ChildSaid = male),
  
  % 4. Parent 2's Statements: "The child is a girl (S2). The child lied (S3)."
  P2SaysS2 = (ChildSex = female),
  P2SaysS3 = (ChildSex \= ChildSaid),

  % 5. Apply Tribal Truth Rules
  % Parent 1 Rule: If male, S1 must be true.
  (P1Sex = male -> P1SaysS1 = true ; true),

  % Parent 2 Rule: 
  % If male, both S2 and S3 must be true.
  % If female, S2 and S3 must be different (one true, one false).
  (P2Sex = male -> (P2SaysS2 = true, P2SaysS3 = true) ; 
    P2Sex = female -> (P2SaysS2 \= P2SaysS3) ; true).