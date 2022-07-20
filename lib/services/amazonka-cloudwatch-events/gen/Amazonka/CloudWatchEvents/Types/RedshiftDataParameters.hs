{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-- Derived from AWS service descriptions, licensed under Apache 2.0.

-- |
-- Module      : Amazonka.CloudWatchEvents.Types.RedshiftDataParameters
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.CloudWatchEvents.Types.RedshiftDataParameters where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude

-- | These are custom parameters to be used when the target is a Amazon
-- Redshift cluster to invoke the Amazon Redshift Data API ExecuteStatement
-- based on EventBridge events.
--
-- /See:/ 'newRedshiftDataParameters' smart constructor.
data RedshiftDataParameters = RedshiftDataParameters'
  { -- | The name or ARN of the secret that enables access to the database.
    -- Required when authenticating using Amazon Web Services Secrets Manager.
    secretManagerArn :: Prelude.Maybe Prelude.Text,
    -- | The name of the SQL statement. You can name the SQL statement when you
    -- create it to identify the query.
    statementName :: Prelude.Maybe Prelude.Text,
    -- | Indicates whether to send an event back to EventBridge after the SQL
    -- statement runs.
    withEvent :: Prelude.Maybe Prelude.Bool,
    -- | The database user name. Required when authenticating using temporary
    -- credentials.
    dbUser :: Prelude.Maybe Prelude.Text,
    -- | The name of the database. Required when authenticating using temporary
    -- credentials.
    database :: Prelude.Text,
    -- | The SQL statement text to run.
    sql :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'RedshiftDataParameters' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'secretManagerArn', 'redshiftDataParameters_secretManagerArn' - The name or ARN of the secret that enables access to the database.
-- Required when authenticating using Amazon Web Services Secrets Manager.
--
-- 'statementName', 'redshiftDataParameters_statementName' - The name of the SQL statement. You can name the SQL statement when you
-- create it to identify the query.
--
-- 'withEvent', 'redshiftDataParameters_withEvent' - Indicates whether to send an event back to EventBridge after the SQL
-- statement runs.
--
-- 'dbUser', 'redshiftDataParameters_dbUser' - The database user name. Required when authenticating using temporary
-- credentials.
--
-- 'database', 'redshiftDataParameters_database' - The name of the database. Required when authenticating using temporary
-- credentials.
--
-- 'sql', 'redshiftDataParameters_sql' - The SQL statement text to run.
newRedshiftDataParameters ::
  -- | 'database'
  Prelude.Text ->
  -- | 'sql'
  Prelude.Text ->
  RedshiftDataParameters
newRedshiftDataParameters pDatabase_ pSql_ =
  RedshiftDataParameters'
    { secretManagerArn =
        Prelude.Nothing,
      statementName = Prelude.Nothing,
      withEvent = Prelude.Nothing,
      dbUser = Prelude.Nothing,
      database = pDatabase_,
      sql = pSql_
    }

-- | The name or ARN of the secret that enables access to the database.
-- Required when authenticating using Amazon Web Services Secrets Manager.
redshiftDataParameters_secretManagerArn :: Lens.Lens' RedshiftDataParameters (Prelude.Maybe Prelude.Text)
redshiftDataParameters_secretManagerArn = Lens.lens (\RedshiftDataParameters' {secretManagerArn} -> secretManagerArn) (\s@RedshiftDataParameters' {} a -> s {secretManagerArn = a} :: RedshiftDataParameters)

-- | The name of the SQL statement. You can name the SQL statement when you
-- create it to identify the query.
redshiftDataParameters_statementName :: Lens.Lens' RedshiftDataParameters (Prelude.Maybe Prelude.Text)
redshiftDataParameters_statementName = Lens.lens (\RedshiftDataParameters' {statementName} -> statementName) (\s@RedshiftDataParameters' {} a -> s {statementName = a} :: RedshiftDataParameters)

-- | Indicates whether to send an event back to EventBridge after the SQL
-- statement runs.
redshiftDataParameters_withEvent :: Lens.Lens' RedshiftDataParameters (Prelude.Maybe Prelude.Bool)
redshiftDataParameters_withEvent = Lens.lens (\RedshiftDataParameters' {withEvent} -> withEvent) (\s@RedshiftDataParameters' {} a -> s {withEvent = a} :: RedshiftDataParameters)

-- | The database user name. Required when authenticating using temporary
-- credentials.
redshiftDataParameters_dbUser :: Lens.Lens' RedshiftDataParameters (Prelude.Maybe Prelude.Text)
redshiftDataParameters_dbUser = Lens.lens (\RedshiftDataParameters' {dbUser} -> dbUser) (\s@RedshiftDataParameters' {} a -> s {dbUser = a} :: RedshiftDataParameters)

-- | The name of the database. Required when authenticating using temporary
-- credentials.
redshiftDataParameters_database :: Lens.Lens' RedshiftDataParameters Prelude.Text
redshiftDataParameters_database = Lens.lens (\RedshiftDataParameters' {database} -> database) (\s@RedshiftDataParameters' {} a -> s {database = a} :: RedshiftDataParameters)

-- | The SQL statement text to run.
redshiftDataParameters_sql :: Lens.Lens' RedshiftDataParameters Prelude.Text
redshiftDataParameters_sql = Lens.lens (\RedshiftDataParameters' {sql} -> sql) (\s@RedshiftDataParameters' {} a -> s {sql = a} :: RedshiftDataParameters)

instance Core.FromJSON RedshiftDataParameters where
  parseJSON =
    Core.withObject
      "RedshiftDataParameters"
      ( \x ->
          RedshiftDataParameters'
            Prelude.<$> (x Core..:? "SecretManagerArn")
            Prelude.<*> (x Core..:? "StatementName")
            Prelude.<*> (x Core..:? "WithEvent")
            Prelude.<*> (x Core..:? "DbUser")
            Prelude.<*> (x Core..: "Database")
            Prelude.<*> (x Core..: "Sql")
      )

instance Prelude.Hashable RedshiftDataParameters where
  hashWithSalt _salt RedshiftDataParameters' {..} =
    _salt `Prelude.hashWithSalt` secretManagerArn
      `Prelude.hashWithSalt` statementName
      `Prelude.hashWithSalt` withEvent
      `Prelude.hashWithSalt` dbUser
      `Prelude.hashWithSalt` database
      `Prelude.hashWithSalt` sql

instance Prelude.NFData RedshiftDataParameters where
  rnf RedshiftDataParameters' {..} =
    Prelude.rnf secretManagerArn
      `Prelude.seq` Prelude.rnf statementName
      `Prelude.seq` Prelude.rnf withEvent
      `Prelude.seq` Prelude.rnf dbUser
      `Prelude.seq` Prelude.rnf database
      `Prelude.seq` Prelude.rnf sql

instance Core.ToJSON RedshiftDataParameters where
  toJSON RedshiftDataParameters' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("SecretManagerArn" Core..=)
              Prelude.<$> secretManagerArn,
            ("StatementName" Core..=) Prelude.<$> statementName,
            ("WithEvent" Core..=) Prelude.<$> withEvent,
            ("DbUser" Core..=) Prelude.<$> dbUser,
            Prelude.Just ("Database" Core..= database),
            Prelude.Just ("Sql" Core..= sql)
          ]
      )
