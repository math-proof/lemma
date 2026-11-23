CREATE TABLE `lemma` (
  id int NOT NULL AUTO_INCREMENT,
  module varchar(256) NOT NULL,
  imports json NOT NULL,
  open json NOT NULL,
  set_option json,
  preamble json NOT NULL,
  lemma json NOT NULL,
  meta json,
  date json NOT NULL,
  PRIMARY KEY (id),
  UNIQUE KEY uq_lemma_module (module)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
