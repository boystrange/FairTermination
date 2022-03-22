{-# OPTIONS --guardedness #-}

module FairTermination (State : Set) (_~>_ : State -> State -> Set) where

import Level using (zero)
open import Axiom.ExcludedMiddle using (ExcludedMiddle)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Empty; Satisfiable; _∪_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Function.Base using (_∘_)

postulate excluded-middle : ExcludedMiddle Level.zero

StateProp : Set₁
StateProp = State -> Set

-- Reflexive and transitive closure of the reduction relation.

_~>*_ : Rel State _
_~>*_ = Star _~>_

-- A state S reduces if S ~> S' for some S' and it is stuck if it
-- does not reduce.

Reduces : StateProp
Reduces S = Satisfiable (S ~>_)

Stuck : StateProp
Stuck S = ¬ (Reduces S)

-- A state is weakly terminating if it has a finite run. A state is
-- non terminating if it is not weakly terminating.

WeaklyTerminating : StateProp
WeaklyTerminating S = ∃[ S' ] S ~>* S' × Stuck S'

NonTerminating : StateProp
NonTerminating S = ¬ WeaklyTerminating S

-- A run is a maximal sequence S ~> S₁ ~> S₂ ~> ..., that is a
-- sequence of reductions that is either infinite or it ends with a
-- stuck state Sₙ.

data Run (S : State) : Set
record ∞Run (S : State) : Set where
  coinductive
  field force : Run S
open ∞Run public

data Run S where
  stop : (stuck : Stuck S) -> Run S
  _::_ : ∀{S'} (red : S ~> S') (ρ : ∞Run S') -> Run S

make-any-run : (S : State) -> ∞Run S
make-any-run S with excluded-middle {Reduces S}
... | yes (S' , red) = λ where .force -> red :: make-any-run S'
... | no stuck = λ where .force -> stop stuck

RunProp : Set₁
RunProp = ∀{S} -> Run S -> Set

-- Each property P of states induces a corresponding property of
-- runs in which there is a state that satisfies P.

data Eventually (P : StateProp) : RunProp where
  here : ∀{S} {ρ : Run S} (proof : P S) -> Eventually P ρ
  next : ∀{S S'} (red : S ~> S') (ρ : ∞Run S') (ev : Eventually P (ρ .force)) -> Eventually P (red :: ρ)

-- Each run that satisfies Eventually P corresponds to a sequence of
-- reductions leading to a state that satisfies P.

pack : ∀{P : StateProp} {S S'} -> S ~>* S' -> P S' -> Σ[ ρ ∈ Run S ] Eventually P ρ
pack ε proof = make-any-run _ .force , here proof
pack (red ◅ reds) proof =
  let ρ , fin = pack reds proof in
  _ , next red (λ where .force -> ρ) fin

unpack : ∀{P : StateProp} {S} {ρ : Run S} -> Eventually P ρ -> ∃[ S' ] S ~>* S' × P S'
unpack (here proof) = _ , ε , proof
unpack (next red ρ fin) =
  let _ , reds , proof = unpack fin in
  _ , red ◅ reds , proof

-- A run is finite if it contains a stuck state. A run is divergent
-- if it contains a non-terminating state.

Finite : RunProp
Finite = Eventually Stuck

Divergent : RunProp
Divergent = Eventually NonTerminating

-- A run is fair if it contains finitely many weakly terminating
-- states. This means that the run is either finite or divergent.

Fair : RunProp
Fair = Finite ∪ Divergent

-- Any state has a fair run. This property (formulated in a slightly
-- different way) is also known as feasibility or machine closure
-- and asserts that the fairness notion we consider "makes sense".

make-fair-run : (S : State) -> Σ[ ρ ∈ Run S ] Fair ρ
make-fair-run S with excluded-middle {WeaklyTerminating S}
... | yes (S' , reds , stuck) = let ρ , fin = pack reds stuck in ρ , inj₁ fin
... | no nwt = make-any-run S .force , inj₂ (here nwt)

-- A state S is fairly terminating if the fair runs of S are finite.

FairlyTerminating : StateProp
FairlyTerminating S = (ρ : Run S) -> Fair ρ -> Finite ρ

-- Here is the alternative characterization of fair termination that
-- does not use fair runs. A state S satisfies the specification if
-- any S' that is reachable from S is weakly terminating.

Specification : StateProp
Specification S = ∀{S'} -> S ~>* S' -> WeaklyTerminating S'

-- Fairness is preserved by ::

::-fair : ∀{S S'} {ρ : ∞Run S'} (red : S ~> S') -> Fair (ρ .force) -> Fair (red :: ρ)
::-fair red (inj₁ fin) = inj₁ (next red _ fin)
::-fair red (inj₂ ent) = inj₂ (next red _ ent)

-- Fair termination is preserved by reductions.

~>-ft : ∀{S S'} -> S ~> S' -> FairlyTerminating S -> FairlyTerminating S'
~>-ft red ft ρ fair with ft (red :: λ where .force -> ρ) (::-fair red fair)
... | here stuck = ⊥-elim (stuck (_ , red))
... | next _ _ fin = fin

~>*-ft : ∀{S S'} -> S ~>* S' -> FairlyTerminating S -> FairlyTerminating S'
~>*-ft ε ft = ft
~>*-ft (red ◅ reds) ft = ~>*-ft reds (~>-ft red ft)

-- Fair termination implies weak termination.

ft->wt : ∀{S} -> FairlyTerminating S -> WeaklyTerminating S
ft->wt {S} ft = let ρ , fair = make-fair-run S in unpack (ft _ fair)

-- Alternative characterization of fair termination.

ft->spec : ∀{S} -> FairlyTerminating S -> Specification S
ft->spec ft reds = ft->wt (~>*-ft reds ft)

spec->ft : ∀{S} -> Specification S -> FairlyTerminating S
spec->ft spec ρ (inj₁ fin) = fin
spec->ft spec ρ (inj₂ div) with unpack div
... | _ , reds , nt = ⊥-elim (nt (spec reds))
