CREATE TABLE `lemma` (
  user varchar(32) NOT NULL,
  module varchar(256) NOT NULL,
  imports json NOT NULL,
  open json NOT NULL,
  set_option json,
  def json NOT NULL,
  lemma json NOT NULL,
  error json,
  date json NOT NULL,
  PRIMARY KEY (user, module)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY() PARTITIONS 8