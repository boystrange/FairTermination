# Fair termination in Agda

The [`FairTermination`](FairTermination.agda) module contains an Agda
formalization of a sound and complete characterization of a **fair termination**
property over an arbitrary reduction system.

## Reduction system

A **reduction system** is a pair (**S**, →) made of a set **S** of **states**
and a **reduction relation** → ⊆ **S** × **S**. We say that S ∈ **S**
**reduces** if there exists S' such that S → S' and we say that S is **stuck**
if S does not reduce.

## Runs and termination properties

A **run** of some state S is a sequence of reductions S → S₁ → S₂ → ⋯ that is
either infinite or such that the last state in the sequence is stuck. Using runs
we can define some well-known termination properties of states. In particular, S
is **strongly terminating** if every run of S is finite, it is **weakly
terminating** if there exists a run of S that is finite, and it is **non
terminating** if every run of S is infinite.

## Fair termination

Fair termination is a termination property weaker than strong termination but
stronger than weak termination. The idea is that, among all the infinite runs of
a given state S, some of them can be considered "unfair" (unrealistic, very
unlikely, etc.) and therefore we can ignore them as far as the termination of S
is concerned. Hereafter, we say that a run is **fair** if it contains finitely
many weakly terminating states. Note that a finite run is always fair, whereas
an infinite run is **unfair** if every state in it is weakly terminating. In
other word, an infinite run represents the execution of a system such that
termination is always within reach, but is never reached. Now, a state S is said
to be **fairly terminating** if every fair run of S is finite.

## Characterization of fair termination

For the particular notion of fair run that we have introduced, it is possible to
provide a sound and complete characterization of fair termination. More
specifically, it can be shown that S is fairly terminating if and only if every
state S' that is reachable from S is weakly terminating.

## References

* Jean-Pierre Queille, Joseph Sifakis, [Fairness and Related Properties in
  Transition Systems - A Temporal Logic to Deal with
  Fairness](https://doi.org/10.1007/BF00265555), Acta Informatica, 1983.
* Nissim Francez, [Fairness](https://doi.org/10.1007/978-1-4612-4886-6),
  Springer, 1986.