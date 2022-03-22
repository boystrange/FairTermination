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

-- A state S reduces if S ~> S' for some S'.

Reduces : StateProp
Reduces S = Satisfiable (S ~>_)

-- A state is stuck if it does not reduce.

Stuck : StateProp
Stuck S = ¬ (Reduces S)

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

RunProp : Set₁
RunProp = ∀{S} -> Run S -> Set

-- A run is finite if it stops and it is infinite if it doesn't.

data Finite : RunProp where
  fin-here : ∀{S} (stuck : Stuck S) -> Finite (stop stuck)
  fin-next : ∀{S S'} (red : S ~> S') (ρ : ∞Run S') (fin : Finite (ρ .force)) -> Finite (red :: ρ)

Infinite : RunProp
Infinite ρ = ¬ Finite ρ

-- A state S is weakly terminating if there is a finite run of S.

WeaklyTerminating : StateProp
WeaklyTerminating S = Σ[ ρ ∈ Run S ] Finite ρ

-- A state S is non terminating if any run of S is infinite.

NonTerminating : StateProp
NonTerminating S = (ρ : Run S) -> Infinite ρ

-- We prove that weak termination and non termination are one the
-- opposite of the other.

¬wt->nt : ∀{S} -> ¬ WeaklyTerminating S -> NonTerminating S
¬wt->nt nwt ρ fin = nwt (ρ , fin)

-- A run is divergent if it contains a non-terminating state.

data Divergent : RunProp where
  div-here : ∀{S} {ρ : Run S} (nt : NonTerminating S) -> Divergent ρ
  div-next : ∀{S S'} (red : S ~> S') (ρ : ∞Run S') (div : Divergent (ρ .force)) -> Divergent (red :: ρ)

div->nt : ∀{S} {ρ : Run S} -> Divergent ρ -> ∃[ S' ] S ~>* S' × NonTerminating S'
div->nt (div-here nt) = _ , ε , nt
div->nt (div-next red ρ div) =
  let S' , reds , nt = div->nt div in
  S' , red ◅ reds , nt

-- A run is fair if it contains finitely many weakly terminating
-- states. This means that the run is either finite or divergent.

Fair : RunProp
Fair = Finite ∪ Divergent

-- A state S is fairly terminating if the fair runs of S are finite.

FairlyTerminating : StateProp
FairlyTerminating S = (ρ : Run S) (fair : Fair ρ) -> Finite ρ

-- Here is the alternative characterization of fair termination that
-- does not use fair runs. A state S satisfies the specification if
-- any S' that is reachable from S is weakly terminating.

Specification : StateProp
Specification S = ∀{S'} -> S ~>* S' -> WeaklyTerminating S'

-- Any state has an arbitrary and a fair run.

make-run : (S : State) -> ∞Run S
make-run S with excluded-middle {Reduces S}
... | yes (S' , red) = λ where .force -> red :: make-run S'
... | no stuck = λ where .force -> stop stuck

make-fair-run : (S : State) -> Σ[ ρ ∈ Run S ] Fair ρ
make-fair-run S with excluded-middle {WeaklyTerminating S}
... | yes (ρ , fin) = ρ , inj₁ fin
... | no nwt with make-run S .force
... | ρ = ρ , inj₂ (div-here (¬wt->nt nwt))

-- Eventual stuckness, eventual non termination and fairness are
-- preserved by ::

::-fair : ∀{S S'} {ρ : ∞Run S'} (red : S ~> S') -> Fair (ρ .force) -> Fair (red :: ρ)
::-fair red (inj₁ fin) = inj₁ (fin-next red _ fin)
::-fair red (inj₂ ent) = inj₂ (div-next red _ ent)

-- Fair termination is preserved by reductions.

~>-ft : ∀{S S'} -> S ~> S' -> FairlyTerminating S -> FairlyTerminating S'
~>-ft red ft ρ fair with ft (red :: λ where .force -> ρ) (::-fair red fair)
... | (fin-next _ _) fin = fin

~>*-ft : ∀{S S'} -> S ~>* S' -> FairlyTerminating S -> FairlyTerminating S'
~>*-ft ε ft = ft
~>*-ft (red ◅ reds) ft = ~>*-ft reds (~>-ft red ft)

-- Fair termination implies weak termination.

ft->wt : ∀{S} -> FairlyTerminating S -> WeaklyTerminating S
ft->wt {S} ft with make-fair-run S
... | ρ , fair with ft ρ fair
... | fin = ρ , fin

-- Alternative characterization of fair termination.

ft->spec : ∀{S} -> FairlyTerminating S -> Specification S
ft->spec ft reds = ft->wt (~>*-ft reds ft)

spec->ft : ∀{S} -> Specification S -> FairlyTerminating S
spec->ft spec ρ (inj₁ fin) = fin
spec->ft spec ρ (inj₂ div) with div->nt div
... | S' , reds , nt with spec reds
... | σ , fin = ⊥-elim (nt σ fin)
