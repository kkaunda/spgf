--import Project.Example

--#eval hi

/-
example (p q r : Prop) : ((p ∨ q) → r ) ↔ ((p → r) Λ (q → r)) :=
begin
 sorry
end
-/
def getGreeting (name : String) := s!"Hello, {name}! isn't lean great!"

def main : IO Unit :=
   let names := ["john","mary","jane"]
   let greetings := names.map getGreeting

   for greeting in greetings do
      IO.println greeting
