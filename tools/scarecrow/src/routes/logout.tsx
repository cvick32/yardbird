import {
  createFileRoute,
  useNavigate,
  useRouter,
} from "@tanstack/react-router";
import { useAuth } from "../AuthProvider";
import { useEffect } from "react";

export const Route = createFileRoute("/logout")({
  component: RouteComponent,
});

function RouteComponent() {
  const auth = useAuth();
  const router = useRouter();
  const navigate = useNavigate();

  useEffect(() => {
    const action = async () => {
      auth.logout();
      await router.invalidate();
      await navigate({ to: "/" });
    };

    action();
  }, []);

  return <div>Logging out...</div>;
}
