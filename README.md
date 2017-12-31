## Welcome to GitHub Pages

## Formalisation of Cryptography - Alan Turing Institute

Welcome to our project. Here we will provide information regarding our project and post past work as well as our vision for the future. We are based at the Alan Turing Institute in London.

Let us start with a little light hearted motivation taken from the Bristol Crypto Groups website. 

"Security proof for even simple cryptographic systems are dangerous and ugly beasts. Luckily, they are only rarely seen: they are usually safely kept in the confines of future full-versions of papers, or only appear in cartoon-ish form, generically labelled as ... proof sketch"

These concerns have been echoed by other well known cryptographers too, for example Bellare and Rogaway in 2004 said,

"In our opinion, many proofs in cryptography have become essentially unverifiable. Our field may be approaching a crisis of rigor". 

The world of formal methods and theorem proving can provide high guarentees of correctness of proofs in this area. We hope the work we are doing here can aid. 

### The Project

Currently we are looking at formalising the area of Multi-Party Computation (MPC). The goal of MPC is for many parties to jointly compute functions on their inputs while keeping their inputs provate. Proofs of security in this area are completed using a simulation-based which is a widely used proof technique in cryptography and little has been done to formalise it. A very thorough introdiction and beyond on the simulation proof technique has been written by Yehuda Lindell (https://eprint.iacr.org/2016/046.pdf). 

We work in the theorem prover Isabelle and with the CryptHOL framework developed by Andreas Lochbilher (https://www.isa-afp.org/entries/CryptHOL.html). This provides a probabilistic programming framework from which we can set up and prove the required security properties of the protocols. This framework was initally designed with the game-based approach to security in mind and we have shown how it can be used to capture simulation based proofs as well. 

#### Work so far

- How to Simulate it in Isabelle: Towards Formal Proof for Multi-Party Computation. ITP 2017. (https://github.com/Davetbutler/formal-crypto-project/blob/master/ITP_2017/How_to_Simulate_in_Isabelle.pdf)

### The People

- David Aspinall - Professor at the University of Edinburgh and a Fellow of the Alan Turing Institute.
- David Butler - Doctoral student at the Alan Turing Institute (University of Edinburgh)
- Adria Gascon - Research Fellow at the Alan Turing Institute.

If you are interested in our work or would like to collaboarate with us please do get in contact.










