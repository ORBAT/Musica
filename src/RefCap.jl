
module RefCap
using AutoHashEquals
using ..Musica

abstract type Abstract end

abstract type TTag <: Abstract end
abstract type TIso <: TTag end
abstract type TBox <: TTag end
abstract type TTrn <: TBox end

abstract type TRef <: TBox end
abstract type TVal <: TBox end

## HOX: trn^ <: trn, trn^ <: val __ja__ trn^ <: ref !!!!
# motherfucker. 

# abstract type RWRightKind end
# # abstract type ReadWrite <: RWRightKind end
# abstract type Write <: RWRightKind end
# abstract type Read <: RWRightKind end

## HOX: vaihtoehto noille abstrakteille tyypeille

abstract type AliasCountKind end
abstract type One <: AliasCountKind end
abstract type Multiple <: One end

# FIXME: pitää saada toimimaan niin, että Global{Multiple} <: Local{One}
abstract type ScopeKind end
abstract type NoneAllowed <: ScopeKind end
abstract type Local{AliasCount} <: NoneAllowed end
abstract type Global{AliasCount} <: Local{AliasCount} end

# NOTE: this is so that ReadWrite <: Read and ReadWrite <: Write
# HOX: are these needed?
# ReadWrite = Tuple{Base.Bottom,Base.Bottom}
# Read = Tuple{Base.Bottom,Nothing}
# Write = Tuple{Nothing,Base.Bottom}

# _Cap{ThisAlias,Read,Write} = Tuple{ThisAlias,Tuple{Read,Write}}
# NOTE: Any in this context doesn't mean it allows anything! This is just so that everything is a subtype of Tag, the most restrictive type
_Tag = Tuple{Any,Any}
_Iso = Tuple{Local{One},Local{One}}
_Box = Tuple{Global{Multiple},Local{Multiple}}
_Trn = Tuple{Local{Multiple},Local{One}}

struct Cap{TRC} end

# iso^ <: trn^
# iso^ <: iso
# trn^ <: val
# trn^ <: ref
# box^ <: box
# val^ <: val
# tag^ <: tag

# iso! <: tag
# trn! <: box

# abstract type TTrn′ <: TRefOrVal end

# abstract type TBox′ <: TBox end
# abstract type TVal′ <: TVal end
# abstract type TVal′ <: TVal end

mutable struct Value{T}
  const _x::T
  _valid_ref_id::Optional{UInt}
end

@auto_hash_equals cache = true struct Reference{RC,T}
  _value::Base.RefValue{T}
  _bound_task_id::Optional{UInt}
end

# TODO: tee `Reference`stä enemmän sellanen object capability-henkinen, et jokanen metodi joka käpistelee sitä palauttaa aina sulle uuden `Reference`n. Esim. `Val` reference ei koskaan invalidoidu, mut sit esim `Reference{Iso}` (ja varmaan `Trn` kans) pitäis jotenkin invalidoitua sen jälkeen ku sen on esim. consumennu tai aliasoinu. 
# Täähän vois toimia niin, että on erillinen `Value{T}` jossa se value _oikeesti_ elää, ja sit tolla `Reference`llä vaan päästään käsiks siihen `Value`en. Et 

# function Reference(_::Type{RC}, value::T) where {RC<:TTag,T}
#   Reference{RC,T}(value, current_task())
# end

# function alias(r::Reference{TRef,T}) where {T}
#   if r.task != current_task()
#     error("alias() can only be called from the task where the Reference was created")
#   end
#   return r.value
# end

end