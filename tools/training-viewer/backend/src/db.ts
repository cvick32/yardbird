import pg from "pg";

const pool = new pg.Pool({
  connectionString:
    process.env.DATABASE_URL ||
    "postgres://cvick-admin:froogy45@localhost:5432/yardbird",
  max: 5,
});

export default pool;
