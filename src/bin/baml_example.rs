use anyhow::Result;
use baml_rust::models::{AnalysisType, VerificationContext, VerificationRequest};
use std::env;
use yardbird::baml_client::BamlClient;

#[tokio::main]
async fn main() -> Result<()> {
    // Check if BAML server is running
    let baml_url = env::var("BAML_URL").unwrap_or_else(|_| "http://localhost:2024".to_string());
    println!("Connecting to BAML server at: {}", baml_url);

    let client = BamlClient::new(Some(baml_url));
    println!("Connected to BAML server");
    // Create a sample verification context based on array_copy.vmt
    let context = VerificationContext {
        variables: vec![
            "i".to_string(), 
            "n".to_string(), 
            "a".to_string(), 
            "b".to_string(),
            "Z".to_string()
        ],
        init_conditions: "(= i 0)".to_string(),
        trans_conditions: "(and (= (store b i (select a i)) b_next) (< i n) (= (+ i 1) i_next) (= a a_next) (= n n_next) (= Z Z_next))".to_string(),
        property: "(=> (and (>= i n) (> Z 0) (< Z n)) (= (select a Z) (select b Z)))".to_string(),
        array_operations: vec!["select".to_string(), "store".to_string()],
        loop_bounds: vec!["(< i n)".to_string()],
        hints: vec!["Array copy loop".to_string()],
    };
    println!("Created Context");

    let request = VerificationRequest {
        analysis_type: AnalysisType::ProposeInvariant,
        context: Box::new(context),
        failed_invariants: vec![],
        counterexample: None,
        current_strategy: Some("Abstract".to_string()),
    };
    println!("Created Request");

    match client.propose_invariant(request).await {
        Ok(suggestions) => {
            println!("BAML Analysis: {}", suggestions.analysis);
            println!("\nProposed Invariants:");
            for (i, candidate) in suggestions.candidates.iter().enumerate() {
                println!("   Type{}: {}", i, candidate.invariant_type);
                println!();
            }

            if !suggestions.strategy_hints.is_empty() {
                println!("Strategy Hints:");
                for hint in &suggestions.strategy_hints {
                    println!("- {}", hint);
                }
            }
        }
        Err(e) => {
            eprintln!("Failed to get invariant suggestions: {}", e);
            eprintln!("Make sure the BAML server is running:");
            eprintln!("  cd baml_schemas && npx baml-cli serve");
        }
    }

    Ok(())
}
