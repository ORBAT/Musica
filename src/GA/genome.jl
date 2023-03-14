using ..Musica
using ..Musica: SizedType
using Transducers, TestItems, Parameters, StaticArrays
using Base: RefValue

#=
# NOTE: genomin mietintää

HUOM LOL, kysäsin GPT-4:ltä. Selittää mun tänhetkisen ajatuksen. Ks alla

eli siis tänhetkinen genomi on ikään kuin aminohapot – yhtä aminohappoa enkoodaa useampi eri (D|R)NA -tripletti (eli kodoni?). Et esim 
aminohappoa valiini enkoodaa (regexinä) GU[GACU]. Jos tän genomin päälle heittää jonkun error correcting coden (ECC), niin se tois siihen 
redundanssia – eri genomit vois dekoodautua samaksi bittisekvenssiksi.

Sit tohon ku heittää insertion, deletion & swap -mutaatiot vielä päälle, niin vois olla jännä.


HOX HOX HOX mitä jos vaan tekis niin, että N bittiä M:stä ei vaan "tee mitään"? Et jos vaikka 1/4, niin 1110 dekoodautuis 111. DNA/RNA:ssa se suhdeluku näyttää olevan 1/3, kun 3sta basesta lähinnä ne 2 ekaa vaikuttaa.

DNA:ssa
3^3 = 27 eli ~4.75bit informaatiota yht
3^2 = 9, eli ~3.17bit informaatiota jää jäljelle


######################### TSÄTTI

totally unrelated, but for `N` bits of "decoded" data, how many bits of error correction do I need to be sure that I always get those `N` bits correct?
ChatGPT

The number of bits required for error detection and correction can vary greatly based on the error correcting code (ECC) you are using and your specific requirements for reliability.

In simple terms, error correcting codes work by adding redundant bits to the data being sent. The number of redundant bits required depends on the number of bits you want to be able to correct.

Here's a brief overview of a few common error correcting codes:

    Parity Check Code: In this simplest form of error detection, only one bit of error can be detected. One parity bit is added to the data to make the number of 1's either always even (even parity) or always odd (odd parity).

    Hamming Code: This is a more sophisticated form of error correction. It introduces parity bits into the data at positions that are powers of 2. The number of parity bits p required to correct one bit error in data length N is such that 2^p >= p + N + 1. For example, to send 4 bits of data (N = 4), you would need 3 parity bits (p = 3), because 2^3 >= 3 + 4 + 1.

    Reed-Solomon Codes: These are block-based error correcting codes commonly used in storage systems and digital communication. The number of error correction bits required depends on the length of the data block and the number of errors you want to be able to correct.

Remember, error correction doesn't come for free - the price you pay is in increased data size and complexity of encoding and decoding the data. In practice, the method you use for error correction will likely be dictated by the specific hardware you are using and the requirements of your application.

Lastly, no error correction code can guarantee 100% error-free transmission, especially in environments with high error rates. These codes can significantly reduce errors, but cannot entirely eliminate them.
User
Hey thanks for the rundown. I'm building a, uh, I guess you could call it a genetic programming system, that instead of using eg. a stack-based VM like StackGP, it does its computation using a sort of pipeline of 1+ cellular automata. Just ECAs so far, and just a linear CA1 -> CA2 -> CA3 pipeline (where each CA in the pipeline is iterated ≥1 times over the input data), but I'm planning to have it eventually evolve networks somehow.

Right now the "genome" is essentially just a Julia `BitVector`, but I've been thinking of moving to something that's more reminiscent of how DNA/RNA codons work; I've understood that for example in RNA the triplets GU[GACU] (excuse my regex, so GUG, GUA etc) all encode for valine.

So I got to thinking whether ECCs could sort of simulate a similar mechanism. I'm thinking of it so that my current parsing where there's no redundancy in the coding (so eg a rule 110 CA can only be produced by a specific bit pattern) is sort of like the amino acids, and then adding an error correcting code on top of that would mean that multiple different "error-corrected genome" bit patterns would decode to the same value, eg. a bit pattern that stands for "instantiate a Rule 110 ECA in this spot".

Now if I also add some things like insertion (add a spurious bit), deletion (delete a random bit) and swap (swap two bits) mutations when doing crossovers, it seems like this could lead to interesting phenomena that are reminiscent of DNA frameshift mutations.

So I guess I most of all want to know whether this sounds viable at all, or if somebody's done something like this before. If you have clarifying questions I'll be happy to answer them
ChatGPT

Your idea sounds very interesting and innovative! From a theoretical perspective, your approach seems viable and could lead to fascinating results. It seems like you're building a genetic algorithm with a particular focus on robustness and fault-tolerance, drawing inspiration from nature's error correcting codes (like the genetic code's redundancy and error correction) and from digital error correction techniques.

As far as I'm aware, there has been some work done in this direction, but it's still an active research area with many possibilities. One of the key challenges with applying error correcting codes to genetic programming is that it can increase the complexity and computational cost of the algorithm. However, the benefits can also be significant: it can improve the robustness and fault-tolerance of the system, and potentially improve the quality of the solutions found by the algorithm.

The phenomena you described, such as frameshift mutations, are indeed interesting and have important implications in genetics. Simulating such mechanisms in genetic algorithms could open up new possibilities in terms of exploring the search space and escaping from local optima.

I suggest you to:

    Keep the Design Simple: Start by implementing the basic error correction and fault-tolerance mechanisms in your genetic algorithm, then gradually add complexity.

    Consider Performance Implications: Error correcting codes can be computationally expensive. You'll need to balance the improved robustness and fault-tolerance against the increased computational cost.

    Experiment and Iterate: Genetic algorithms are very much an empirical science. Try out different approaches and see what works best.

    Stay Updated with Relevant Research: Keep reading the latest research papers and articles related to genetic programming and error correcting codes. You can also consider reaching out to researchers or joining relevant forums or communities.

As you refine your algorithm and system, you may also want to consider publishing your findings. This kind of interdisciplinary work between genetics, error correction, and genetic programming could potentially be valuable to others working in these fields.
User
hey thanks! So what would be good "inexpensive" ECCs I could explore? As far as I understand it, eg parity bits that you mentioned can only be used for _check_ for errors but not correct them
ChatGPT

You're correct that parity bits can only be used for error detection, not correction. For error correction, you'll need to use a more sophisticated method. Here are a few relatively simple error correction codes (ECCs) that you could consider:

    Hamming Codes: Hamming codes are a family of linear error-correcting codes that generalize the parity-check code. They can detect up to two-bit errors or correct one-bit errors without detection of uncorrected errors. In terms of complexity, Hamming codes are a good starting point.

    Repetition Codes: In a repetition code, each bit of data is repeated a certain number of times. For example, in a 3-bit repetition code, each bit would be repeated three times. Repetition codes are simple, but they are not very efficient because they require a lot of extra bits. However, they can be a good choice if your goal is to create a simple proof of concept.

    BCH Codes: BCH (Bose–Chaudhuri–Hocquenghem) codes are a class of cyclic error-correcting codes that are constructed using polynomials over a finite field. BCH codes are more complex than Hamming codes, but they can correct more errors.

    Reed-Solomon Codes: Reed-Solomon codes are a type of BCH code that can correct multiple symbol errors. They are used in many practical systems, including the Compact Disc and the QR Code.

All of these ECCs have different trade-offs in terms of complexity, error correction capability, and overhead (i.e., the number of extra bits required). I'd recommend starting with the simplest option (like Hamming codes or repetition codes) and then moving on to more sophisticated methods if needed.

Keep in mind that in a genetic programming context, the goal of using ECCs is not necessarily to ensure perfect transmission of data, but rather to add robustness to the system and potentially introduce interesting dynamics (like the frameshift mutations you mentioned earlier).
User
Yeah exactly! I don't want an ECC that's _too_ good. Repetition feels like it might not be a good fit, but I'll have to research the others. I _think_ I'd want a block code to simulate how DNA is… uh… "parsed"
ChatGPT

Yes, you're on the right track. Block codes, which encode a block of input data as a larger block of output data, would be a good match for simulating the coding and decoding process of DNA. Both Hamming codes and BCH codes (including Reed-Solomon codes) are examples of block codes.

As an alternative, you might also consider convolutional codes, which encode the entire data stream bit-by-bit, and are used in applications where data is transmitted continuously. They are a bit more complex than block codes but can offer better performance in terms of error correction.

Remember that error correction codes are designed to add robustness to the transmission of data, but in your case, you're not necessarily interested in perfect transmission. You may want to explore the impact of different error rates and how they affect the evolution of your genetic programming system.

Good luck with your project! This kind of interdisciplinary work can be challenging, but it also has the potential to lead to innovative and interesting results.

=#


const default_genome_codon_length::Int = 6
const default_genome_redundant_per_codon::Int = 2
const default_max_codons::Int = 400

"""
- `ElemType` on yksittäisen "emäksen" tyyppi. Kun `NStates` == 2 niin defaultti on `Bool`
- `NStates` kertoo kuinka monta "basea" genomissa on. Binäärikamassa `NStates` == 2. DNA:ssa `NStates` = 4 (A, C, G, T)
- `CodonLen` on yksittäisen "kodonin" kokonaispituus. Jokaisesta kodonista tiputetaan `NRedundant` viimeistä elementtiä pois


KYS: `ElemType` ei oikein oo järkevän oloinen. Pitäis ehkä olla dekoodaamattoman genomin tyyppi?
--> eiköhän se oo jees. Dekoodaamaton on `AbstractArray{ElemType}`, dekoodattu sit joku tyyliin Vector{SVector{CodonLen,ElemType}}
HOX HOX: eiku dekoodattu vois hyvin olla `Vector` jonka elementit on `SizedVector{CodonLen}(@view genome[i:i+CodonLen-1])`
"""
@with_kw struct GenomeOptions{ElemType,CodonLen,NRedundant,NStates}
    max_codons::Int = default_max_codons
    min_codons::Int = 3

    Base.@propagate_inbounds function GenomeOptions{ElemType,CodonLen,NRedundant,NStates}(
        max_codons,
        min_codons) where {ElemType,CodonLen,NRedundant,NStates}
        @boundscheck @assert NRedundant < CodonLen
        @boundscheck @assert max_codons ≥ min_codons
        new{ElemType,CodonLen,NRedundant,NStates}(max_codons, min_codons)
    end
end

function GenomeOptions{CodonLen,NRedundant}(; restkw...) where {CodonLen,NRedundant}
    GenomeOptions{Bool,CodonLen,NRedundant,2}(; restkw...)
end

"""
NOTE: tää on sitä varten että Parameters.@with_kw:n luomat konstruktorit toimii ilman tyyppiparametreja, eli
GenomeOptions() ja GenomeOptions(max_codons=50) 
"""
function GenomeOptions(maxc, minc)
    GenomeOptions{Bool,default_genome_codon_length,default_genome_redundant_per_codon,2}(maxc, minc)
end

# function Base.show(io::IO, opts::GenomeOptions{NS,CL,NR}) where {NS,CL,NR}

# end

@inline genome_max_length(opts::GenomeOptions{NS,CodonLen}) where {NS,CodonLen} = CodonLen * opts.max_codons
@inline genome_min_length(opts::GenomeOptions{NS,CodonLen}) where {NS,CodonLen} = CodonLen * opts.min_codons

# HOX: hoitaa vaan maksimin
function clamp_genome_length!(opts::GenomeOptions{T,CL,NR}, genome) where {T,CL,NR}
    # TODO FIXME: minimin hanskaus
    let max_len = genome_max_length(opts)
        if length(genome) > max_len
            resize!(genome, max_len)
        end
    end
    genome
end

function genome_length_extrema(go::GenomeOptions{NS,CL}) where {NS,CL}
    genome_min_length(go), genome_max_length(go)
end


@inline active_codon_length(::Type{<:GenomeOptions{T,CodonLen,NRedundant}}) where {T,CodonLen,NRedundant} = CodonLen - NRedundant
@inline active_codon_length(::T) where {T<:GenomeOptions} = active_codon_length(T)

@inline redundant_per_codon(::Type{<:GenomeOptions{T,CL,NR}}) where {T,CL,NR} = NR
@inline redundant_per_codon(::GO) where {GO<:GenomeOptions} = redundant_per_codon(GO)

@inline codon_length(::Type{<:GenomeOptions{T,CodonLen}}) where {T,CodonLen} = CodonLen
@inline codon_length(::T) where {T<:GenomeOptions} = codon_length(T)

function decode_genome(opts::GenomeOptions{T,CodonLen,NRedundant}, genome)::Transducers.Eduction where {T,CodonLen,NRedundant}
    genome |>
    Partition(CodonLen; flush=true) |>
    Map(
        @<(ZeroPadded{active_codon_length(opts)}()) ∘
        @<(droplast(NRedundant, CodonLen)) ∘
        copy
    )
end

# function GenomeDecoder(opts::GenomeOptions, genome)
#     Iterators.partition(genome, opts.codon_length) |>
#     # genome |> Partition(opts.codon_length; flush=true) |> Map(copy) |>
#     MapCat(
#         @<(_zero_pad_array(opts.codon_length - opts.redundant_per_codon)) ∘
#         @<(_droplast(opts.redundant_per_codon, opts.codon_length))
#     )
# end

# struct GenomeDecoder{OrigT,DecFn}
#     orig_genome::OrigT
#     xf::DecFn
# end

#  (dg::GenomeDecoder{CL,NR})() where {CL,NR} 
# #     decode_genome(dg.genome, )
# # end

@testitem "genome mappings" begin
    let opts = GA.GenomeOptions{GA.default_genome_codon_length,GA.default_genome_redundant_per_codon}(max_codons=1000, min_codons=1)
        @test GA.decode_genome(opts, 1:15 |> collect) |> collect == [
            [1, 2, 3, 4],
            [7, 8, 9, 10],
            [13, 14, 15, 0]]

        # nää on kaikki keskenään samoja, koska 1:17 ja 1:18 lisää vaan 1 tai 2 redundanttia kodonia, eli niitä ei tuu dekoodattuun outputtiin yhtään.
        @test GA.decode_genome(opts, 1:16) |> collect ==
              GA.decode_genome(opts, 1:17) |> collect ==
              GA.decode_genome(opts, 1:18) |> collect
    end
    let genome = 1.0:14.0 |> collect, opts = GA.GenomeOptions{Float64,4,1,2}()
        @test GA.decode_genome(opts, genome) |> collect == [
            [1.0, 2.0, 3.0],
            [5.0, 6.0, 7.0],
            [9.0, 10.0, 11.0],
            [13.0, 14.0, 0.0]]
    end

end

#=
ks Bear / Neuroevoluutiopläni

The presence of a gene in the genome is sig- naled by the presence of a promoter, that is, a predefined sequence of fixed length. A gene is constituted by a fixed, predefined number of characters following a promoter. In Reil [63], an activated gene produces another sequence of characters which is a transliterated version of the gene. The new sequence is interpreted as a regulatory protein. If a regulatory protein matches exactly a sequence of char- acters in the genome, it regulates the expression of the gene that immediately follows the matched genome sequence (see Fig. 8). The regulation can be positive or negative, and is of the on-off type, with repression pre- vailing over activation.


=#

const Codon{CodonLen, Elem} = SizedType{CodonLen,Elem}
const CodonSeq{CodonLen,Elem} = AbstractArray{Codon{CodonLen,Elem}}

abstract type AbstractGeneticSeq{CodonLen,Elem} end

struct Gene{CodL,E,Codons<:CodonSeq{CodL,E}} <: AbstractGeneticSeq{CodL,E}
    position::Tuple{Int, Int} # start, stop
    coding_region::Codons
    # where do I put enhancers and silencers that are acting on the gene?
end

struct Operon{CodL,E,Cs<:CodonSeq{CodL,E},Gs<:AbstractArray{Gene{CodL,E}}} <: AbstractGeneticSeq{CodL,E}
    position::Tuple{Int, Int} # start, stop
    regulatory_region::Cs # operator & promoter
    codons::Cs #     decoded into 0+ `Gene`s
    _decoded_genes::RefValue{Musica.Optional{Gs}}
end

# struct Intron{T}
#     xs::T
# end

# struct Exon{T}
#     xs::T
# end

get_start_position(o::AbstractGeneticSeq) = o.position[1]
get_stop_position(o::AbstractGeneticSeq) = o.position[2]