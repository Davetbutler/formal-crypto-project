
## Formalisation of Cryptography at the Alan Turing Institute

Currently we are looking at formalising the area of Multi-Party Computation (MPC). The goal of MPC is for many parties to jointly compute functions on their inputs while keeping their inputs private. Proofs of security in this area are completed using simulation-based proofs which are widely used in cryptography. A very thorough introduction and beyond on the simulation proof technique has been written by Yehuda Lindell and can be found [here](https://eprint.iacr.org/2016/046.pdf). 

We work in the theorem prover Isabelle and in particular with the [CryptHOL](https://www.isa-afp.org/entries/CryptHOL.html) framework developed by Andreas Lochbihler. This provides a probabilistic programming framework from which we can set up and prove the required security properties of the protocols. This framework was initally designed with the game-based approach to security in mind and we have shown how it can be used to capture simulation based proofs as well. 

## Work so far

- How to Simulate it in Isabelle: Towards Formal Proof for Multi-Party Computation. ITP 2017. The paper can be viewed [here](https://github.com/Davetbutler/formal-crypto-project/blob/master/ITP_2017/How_to_Simulate_in_Isabelle.pdf).

## Ongoing and Future Work

We are currently looking at formalising proofs of security for larger MPC protocols as well as other fundamental primitives like commitment schemes.

## The People

- David Aspinall - Professor at the University of Edinburgh and a Fellow of the Alan Turing Institute.
- David Butler - Doctoral student at the Alan Turing Institute (University of Edinburgh) (dbutler@turing.ac.uk)
- Adria Gascon - Research Fellow at the Alan Turing Institute.

If you are interested in our work or would like to collaboarate with us please do get in contact!










