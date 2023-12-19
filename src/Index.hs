module Index where

type IndexVariableId = String

data Index
    = IndexVariable IndexVariableId
    | Number Int
    | Plus Index Index

type IndexContext = [IndexVariableId]