CREATE TABLE `docstring` (
  id int NOT NULL COMMENT 'Owning axiom.lemma row ID',
  lemma_id int NOT NULL COMMENT 'Zero-based declaration index in the Lean file',
  text text NOT NULL,
  PRIMARY KEY (id, lemma_id),
  FULLTEXT KEY ft_docstring (text)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
